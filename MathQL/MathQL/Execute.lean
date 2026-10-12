import MathQL.Compile
import MathQL.Database
import MathQL.Backend
import Lean.Data.Json

/-! Execution of a type-checked query against a database connection, producing a
JSON array of result rows. Each output column is read at its declared type and
rendered to JSON; a NULL cell becomes JSON `null`. -/

namespace MathQL

/-- Read one row's output columns, keyed by their aliases, in output order. -/
def rowObject (cursor : Cursor) (cs : List (Ident × Ty × Expr)) :
    IO (List (Ident × Lean.Json)) := do
  cs.zipIdx.mapM fun ((x, t, _), i) => do
    let v ← cursor.readCell i t
    return (x, v)

/-- A runtime environment for postprocessing expressions -/
structure PostEnvironment where
  ident : List (Ident × Lean.Json)
  function : List (Ident × (List Lean.Json → Result Lean.Json))

/-- Recoverable absence becomes JSON null at each expression boundary;
integer overflow must fail the whole query. -/
inductive PostError where
  | absent : String → PostError
  | overflow : PostError

abbrev PostResult := Except PostError

private def liftPost {α : Type} (r : Result α) : PostResult α := r.mapError .absent

private def postInteger (n : Int) : PostResult Lean.Json :=
  if integerInRange n then .ok (.num n) else .error .overflow

/-- An absent subexpression is a value its parent can handle, not an early exit
from the entire output field. Never turn fatal arithmetic errors into null. -/
private def nullOnAbsence : PostResult Lean.Json → PostResult Lean.Json
  | .error (.absent _) => .ok .null
  | result => result

def evalUnaryOp : UnaryOp → Lean.Json → PostResult Lean.Json
| _, .null => return .null
| .not, j => do
  let b ← liftPost j.getBool?
  return .bool (not b)
| .neg, j => do
  let k ← liftPost j.getInt?
  postInteger (- k)

def evalBinaryOp : BinaryOp → Lean.Json → Lean.Json → PostResult Lean.Json
-- SQL three-valued logic: a decisive boolean wins even when the other is null.
| .and, .bool false, _ | .and, _, .bool false => return .bool false
| .or, .bool true, _ | .or, _, .bool true => return .bool true
| _, .null, _ | _, _, .null => return .null
| .and, v1, v2 => do
  let b1 ← liftPost v1.getBool?
  let b2 ← liftPost v2.getBool?
  return .bool (b1 && b2)
| .or, v1, v2 => do
  let b1 ← liftPost v1.getBool?
  let b2 ← liftPost v2.getBool?
  return .bool (b1 || b2)
| .add, v1, v2 => do
  let k1 ← liftPost v1.getInt?
  let k2 ← liftPost v2.getInt?
  postInteger (k1 + k2)
| .sub, v1, v2 => do
  let k1 ← liftPost v1.getInt?
  let k2 ← liftPost v2.getInt?
  postInteger (k1 - k2)
| .mul, v1, v2 => do
  let k1 ← liftPost v1.getInt?
  let k2 ← liftPost v2.getInt?
  postInteger (k1 * k2)
| .div, v1, v2 => do
  let k1 ← liftPost v1.getInt?
  let k2 ← liftPost v2.getInt?
  if k2 == 0 then return .null else postInteger (k1.tdiv k2)

/-- Compare two JSON values at their MathQL type. -/
def compareJson : Ty → Lean.Json → Lean.Json → Result Ordering
| .int, j1, j2 => do
  let k1 ← j1.getInt?
  let k2 ← j2.getInt?
  return compare k1 k2
| .bool, j1, j2 => do
  let b1 ← j1.getBool?
  let b2 ← j2.getBool?
  return compare b1 b2
| .string, j1, j2 => do
  let s1 ← j1.getStr?
  let s2 ← j2.getStr?
  return compare s1 s2
| .list _, j1, j2
| .prod _, j1, j2 => return compare j1.compress j2.compress

def evalComparison (op : ComparisonOp) (t : Ty) (j1 : Lean.Json) (j2 : Lean.Json) :
    Result Lean.Json :=
  match j1, j2 with
  | .null, _ | _, .null => return .null
  | _, _ => do
    let c ← compareJson t j1 j2
    return .bool <|
      match op with
      | .eq => c.isEq
      | .ne => c.isNe
      | .lt => c.isLT
      | .le => c.isLE
      | .gt => c.isGT
      | .ge => c.isGE

/-- Presence tests must not hide a fatal arithmetic error. -/
def isDefined : PostResult Lean.Json → PostResult Bool
| .ok .null | .error (.absent _) => .ok false
| .error .overflow => .error .overflow
| .ok _ => .ok true

/-- Evaluate each subexpression to a nullable value. Normalizing recoverable
absence here makes direct failures and previously decoded nulls interchangeable. -/
def evalPostExpr (env : PostEnvironment) (expr : Expr) : PostResult Lean.Json :=
  nullOnAbsence <| match expr with
  | .int n => postInteger n

  | .unop .neg (.int n) => postInteger (-n)

  | .bool b => return .bool b

  | .str s => return .str s

  | .ident x =>
    match env.ident.lookup x with
    | none => throw (.absent s!"unknown identifier {x.name}")
    | some v => return v

  | .id _ =>
    throw (.absent "id is not allowed in postprocessing")

  | .field _ _ =>
    throw (.absent "field projection is not allowed in postprocessing")

  | .call f args =>
    match env.function.lookup f with
    | .none => throw (.absent s!"unknown function {f.name}")
    | .some f => do
      let vs ← args.mapM (evalPostExpr env)
      let v ← liftPost (f vs)
      match v with
      | .num _ => postInteger (← liftPost v.getInt?)
      | _ => return v

  | .unop op e => do
    let v ← evalPostExpr env e
    evalUnaryOp op v

  | .binop op e1 e2 => do
    let v1 ← evalPostExpr env e1
    let v2 ← evalPostExpr env e2
    evalBinaryOp op v1 v2

  | .compare op t e1 e2 => do
    let v1 ← evalPostExpr env e1
    let v2 ← evalPostExpr env e2
    liftPost (evalComparison op t v1 v2)

  | .list _ es => do
    let vs ← es.mapM (evalPostExpr env)
    return .arr vs.toArray

  | .tuple _ es => do
    let vs ← es.mapM (evalPostExpr env)
    return .arr vs.toArray

  | .proj _ e1 n => do
    let v ← evalPostExpr env e1
    liftPost (v.getArrVal? n)

  | .ite b e1 e2 => do
    let b ← evalPostExpr env b
    match b with
    | .bool true => evalPostExpr env e1
    | .bool false | .null => evalPostExpr env e2
    | _ => throw (.absent "boolean expected")

  | .defined e => do
    return .bool (← isDefined (evalPostExpr env e))

  | .undefined e => do
    return .bool (not (← isDefined (evalPostExpr env e)))


def evalPostprocess (env : PostEnvironment) :
  List (Ident × Ty × Expr) → Result (List (Ident × Lean.Json))
| [] => return []
| (x, _, e) :: ps => do
  let v ← match evalPostExpr env e with
    | .ok v => pure v
    | .error (.absent _) => pure .null
    | .error .overflow => throw "integer overflow: outside signed 64-bit range"
  let vs ← evalPostprocess {env with ident := (x, v) :: env.ident} ps
  return (x, v) :: vs

/-- Step through every result row, decoding each into its output object. -/
partial def collectRows
  (funs : List (Ident × (List Lean.Json → Result Lean.Json)))
  (cursor : Cursor)
  (q : Query)
  (acc : Array (List (Ident × Lean.Json))) :
    IO (Array (List (Ident × Lean.Json))) := do
  if ← cursor.next then
    let row ← rowObject cursor q.output
    let post ← match evalPostprocess {ident := row, function := funs} q.postprocess with
      | .ok post => pure post
      | .error e => throw (IO.userError e)
    collectRows funs cursor q (acc.push (row ++ post))
  else
    return acc

/-- Encode an output row in the transport's ordered name/value format. -/
def fieldsToJson (lst : List (Ident × Lean.Json)) : Lean.Json :=
  .arr (lst.map (fun (x, j) => .arr #[.str x.name, j])).toArray

/-- Run a checked query; driver and decoding failures become protocol errors. -/
def run (db : Connection) (D : Database) (isSafeAlias : String → Bool) (q : Query) :
    IO (Except String Lean.Json) := do
  match compileQueryWith db.dialect D isSafeAlias q with
  | .error e => return .error e
  | .ok sql =>
    try
      let cursor ← db.prepare (SQL.renderQueryWith db.dialect sql)
      let rows ← collectRows (D.postFunction.map (fun ⟨f,_,c⟩ => (f, c))) cursor q #[]
      return .ok (Lean.Json.arr (rows.map fieldsToJson))
    catch e => return .error e.toString

end MathQL
