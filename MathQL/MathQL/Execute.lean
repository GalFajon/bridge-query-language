import MathQL.Compile
import MathQL.Database
import SQLite
import Lean.Data.Json

/-! Execution of a type-checked query against a SQLite connection, producing a
JSON array of result rows. Each output column is read at its declared type and
rendered to JSON; a NULL cell becomes JSON `null`. -/

namespace MathQL

/-- Read one output column at its declared type, as JSON; a NULL cell is `null`.
Lists and products are stored as JSON text and returned verbatim. -/
def decodeCell : Ty → SQLite.RowReader Lean.Json
  | .int => do
    let o : Option Int64 ← SQLite.RowReader.field
    return match o with | some i => Lean.toJson i.toInt | none => Lean.Json.null
  | .bool => do
    let o : Option Bool ← SQLite.RowReader.field
    return match o with | some b => Lean.toJson b | none => Lean.Json.null
  | .string => do
    let o : Option String ← SQLite.RowReader.field
    return match o with | some s => Lean.toJson s | none => Lean.Json.null
  | .list _ | .prod _ => do
    let o : Option String ← SQLite.RowReader.field
    match o with
    | none => return Lean.Json.null
    | some s =>
      match Lean.Json.parse s with
      | .ok j => return j
      | .error e => throw (IO.userError s!"expected JSON in a list or product column: {e}")

/-- Read one row's output columns, keyed by their aliases, in output order. -/
def rowObject (cs : List (Ident × Ty × Expr)) : SQLite.RowReader (List (Ident × Lean.Json)) := do
  cs.mapM fun (x, t, _) => do
    let v ← decodeCell t
    return (x, v)

/-- A runtime environment for postprocessing expressions -/
structure PostEnvironment where
  ident : List (Ident × Lean.Json)
  function : List (Ident × (List Lean.Json → Result Lean.Json))

def evalUnaryOp : UnaryOp → Lean.Json → Result Lean.Json
| .not, j => do
  let b ← j.getBool?
  return .bool (not b)
| .neg, j => do
  let k ← j.getInt?
  return .num (- k)

def evalBinaryOp : BinaryOp → Lean.Json → Lean.Json → Result Lean.Json
| .and, v1, v2 => do
  let b1 ← v1.getBool?
  let b2 ← v2.getBool?
  return .bool (b1 && b2)
| .or, v1, v2 => do
  let b1 ← v1.getBool?
  let b2 ← v2.getBool?
  return .bool (b1 || b2)
| .add, v1, v2 => do
  let k1 ← v1.getInt?
  let k2 ← v2.getInt?
  return .num (k1 + k2)
| .sub, v1, v2 => do
  let k1 ← v1.getInt?
  let k2 ← v2.getInt?
  return .num (k1 - k2)
| .mul, v1, v2 => do
  let k1 ← v1.getInt?
  let k2 ← v2.getInt?
  return .num (k1 * k2)

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

/-- Whether a result is a non-null value; a failure counts as null. -/
def isDefined : Result Lean.Json → Bool
| .ok .null | .error _ => false
| .ok _ => true

def evalPostExpr (env : PostEnvironment) : Expr → Result Lean.Json

| .int n => return .num n

| .bool b => return .bool b

| .str s => return .str s

| .ident x =>
  match env.ident.lookup x with
  | none => throw s!"unknown identifier {x.name}"
  | some v => return v

| .id _ =>
  throw s!"id is not allowed in postprocessing"

| .field _ _ =>
  throw s!"field projection is not allowed in postprocessing"

| .call f args =>
  match env.function.lookup f with
  | .none => throw s!"unknown function {f.name}"
  | .some f => do
    let vs ← args.mapM (evalPostExpr env)
    f vs

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
  evalComparison op t v1 v2

| .list _ es => do
  let vs ← es.mapM (evalPostExpr env)
  return .arr vs.toArray

| .tuple _ es => do
  let vs ← es.mapM (evalPostExpr env)
  return .arr vs.toArray

| .proj _ e1 n => do
  let v ← evalPostExpr env e1
  v.getArrVal? n -- We're relying here on Result = Except String

| .ite b e1 e2 => do
  let b ← evalPostExpr env b
  match b.getBool? with
  | .ok true => evalPostExpr env e1
  | .ok false => evalPostExpr env e2
  | .error msg => throw s!"boolean expected ({msg})"

| .defined e =>
  return .bool (isDefined (evalPostExpr env e))

| .undefined e =>
  return .bool (not (isDefined (evalPostExpr env e)))


def evalPostprocess (env : PostEnvironment) :
  List (Ident × Ty × Expr) → List (Ident × Lean.Json)
| [] => []
| (x, _, e) :: ps =>
  let v := match evalPostExpr env e with | .ok v => v | .error _ => .null
  let vs := evalPostprocess {env with ident := (x, v) :: env.ident} ps
  (x, v) :: vs

/-- Step through every result row, decoding each into its output object. -/
partial def collectRows
  (funs : List (Ident × (List Lean.Json → Result Lean.Json)))
  (stmt : SQLite.Stmt)
  (q : Query)
  (acc : Array (List (Ident × Lean.Json))) :
    IO (Array (List (Ident × Lean.Json))) := do
  if ← stmt.step then
    let row ← (rowObject q.output).run stmt
    let post := evalPostprocess {ident := row, function := funs} q.postprocess
    collectRows funs stmt q (acc.push (row ++ post))
  else
    return acc

/-- Run a type-checked query against an open SQLite connection, as a JSON array of rows. -/
def run (db : SQLite) (D : Database) (isSafeAlias : String → Bool) (q : Query) :
    IO (Except String Lean.Json) := do
  match compileQuery D isSafeAlias q with
  | .error e => return .error e
  | .ok sql =>
    let stmt ← db.prepare (toString sql)
    let rows ← collectRows (D.postFunction.map (fun ⟨f,_,c⟩ => (f, c))) stmt q #[]
    return .ok (Lean.Json.arr (rows.map fieldsToJson))
where
  fieldsToJson (lst : List (Ident × Lean.Json)) : Lean.Json :=
    .arr (lst.map (fun (x, j) => .arr #[.str x.name, j])).toArray

end MathQL
