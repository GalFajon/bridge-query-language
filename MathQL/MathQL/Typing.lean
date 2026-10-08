import MathQL.Input
import MathQL.Result
import MathQL.Context
import MathQL.Expr
import MathQL.Rules
import MathQL.Database
import MathQL.Query

namespace MathQL

mutual

/-- Check that `e` elaborates to a typed expression of type `t` in context `Γ`.
    Checking forms are handled here; inferring forms delegate to `infer`. -/
def check (Γ : Context) (e : Input.Expr) (t : Ty) : Result { e' : Expr // ExprOfTy Γ e' t } :=
  match e with

  | .list es =>
    match t with
    | .list t => do
      let ⟨es, hes⟩ ← checkList Γ t es
      return ⟨.list t es, .list hes⟩
    | _ => throw s!"expected {t}, but got a list"

  | .ite e₁ e₂ e₃ => do
    let ⟨c, hc⟩ ← check Γ e₁ .bool
    let ⟨a, ha⟩ ← check Γ e₂ t
    let ⟨b, hb⟩ ← check Γ e₃ t
    return ⟨.ite c a b, .ite hc ha hb⟩

  | .tuple es =>
    match t with
    | .prod ts => do
      let ⟨es', h⟩ ← checkTuple Γ es ts
      return ⟨.tuple ts es', .tuple h⟩
    | _ => throw s!"expected {t}, but got a tuple"

  | e => do
    let ⟨t', e', h⟩ ← infer Γ e
    if heq : t' == t then .ok ⟨e', Ty.eq_of_beq t' t heq ▸ h⟩
    else throw s!"type mismatch: expected {t}, but got {t'}"

/-- Infer a type for `e` in context `Γ`, elaborating it to a typed expression.
    Inferring forms are handled here; checking-only forms are an error. -/
def infer (Γ : Context) (e : Input.Expr) : Result (Σ (t : Ty), { e' : Expr // ExprOfTy Γ e' t }) :=
  match e with

  | .int n => pure ⟨.int, .int n, .int⟩

  | .bool b => pure ⟨.bool, .bool b, .bool⟩

  | .str s => pure ⟨.string, .str s, .str⟩

  | .ident x' => do
    let x := .ident x'
    let ⟨t, h⟩ ← (Γ.getIdent x).attach
    return ⟨t, .ident x, .ident h⟩

  | .id e => do
    let ⟨d, e, he⟩ ← inferDomain Γ e
    let ⟨ts, ht⟩ ← (Γ.getIdTys d).attach
    return ⟨.prod' ts, .id e, .id he ht rfl⟩

  | .obj _ _ =>
    throw s!"a bare object cannot appear in an expression"

  | .field e l' => do
    let l := Label.label l'
    let ⟨d, e, he⟩ ← inferDomain Γ e
    let ⟨t, ht⟩ ← (Γ.getInputFieldTy d l).attach
    return ⟨t, .field e l, .field he ht⟩

  | .proj e idx => do
    let ⟨te, e', he⟩ ← infer Γ e
    match te, he with
    | .prod ts, hp =>
      match h : ts[idx]? with
      | some t => .ok ⟨t, .proj t e' idx, .proj hp h⟩
      | none => throw s!"projection index {idx} out of range"
    | _, _ => throw "projection of a non-product"

  | .call f' es =>
    let f := .ident f'
    match h : Γ.function.lookup f with
    | none => throw s!"unknown function {f'}"
    | some (ts, t) => do
      let ⟨es, hes⟩ ← checkTuple Γ es ts
      return ⟨t, .call f es, .call h hes⟩

  | .unop op e =>
    match h : unaryTy op with
    | (t₁, t₂) => do
      let ⟨e, he⟩ ← check Γ e t₁
      pure ⟨t₂, .unop op e, .unop h he⟩

  | .binop op e₁ e₂ =>
    match h : binaryTy op with
    | (t₁, t₂, t₃) => do
      let ⟨e₁, h₁⟩ ← check Γ e₁ t₁
      let ⟨e₂, h₂⟩ ← check Γ e₂ t₂
      return ⟨t₃, .binop op e₁ e₂, .binop h h₁ h₂⟩

  | .compare op e₁ e₂ => do
    let ⟨t, e₁, h₁⟩ ← infer Γ e₁
    let ⟨e₂, h₂⟩ ← check Γ e₂ t
    return ⟨.bool, .compare op t e₁ e₂, .compare h₁ h₂⟩

  | .defined e => do
    let ⟨_, e, he⟩ ← infer Γ e
    return ⟨.bool, .defined e, .defined he⟩

  | .undefined e => do
    let ⟨_, e', he⟩ ← infer Γ e
    return ⟨.bool, .undefined e', .undefined he⟩

  | .list [] => throw "cannot infer the type of this empty list"

  | .list (e :: es) => do
    let ⟨t, e, he⟩ ← infer Γ e
    let ⟨es, hes⟩ ← checkList Γ t es
    return ⟨.list t, .list t (e :: es), .list (.cons he hes)⟩

  | .ite e₁ e₂ e₃ => do
    let ⟨c, hc⟩ ← check Γ e₁ .bool
    let ⟨t, a, ha⟩ ← infer Γ e₂
    let ⟨b, hb⟩ ← check Γ e₃ t
    return ⟨t, .ite c a b, .ite hc ha hb⟩

  | .tuple es => do
    let ⟨ts, es', h⟩ ← inferTuple Γ es
    return ⟨.prod ts, .tuple ts es', .tuple h⟩

def inferDomain (Γ : Context) (e : Input.Expr) :
  Result (Σ (d : DomainName), { e : Domain // DomainOfTy Γ e d})
  := do
  match e with

  | .ident x' => do
    let x := .ident x'
    let ⟨d, h⟩ ← (Γ.getDomainIdent x).attach
    return ⟨d, .ident x, .ident h⟩

  | .obj d' es => do
    let d := .domain d'
    let ⟨ts, ht⟩ ← (Γ.getIdTys d).attach
    let ⟨es, he⟩ ← checkTuple Γ es ts
    return ⟨d, .obj d es, .obj ht he⟩

  | .field e f' => do
    let f := Label.label f'
    let ⟨d, e, he⟩ ← inferDomain Γ e
    let ⟨dn, hd⟩ ← (Γ.getDomainField d f).attach
    return ⟨dn, .field e f, .field he hd⟩

  | .int _  | .bool _ | .str _ | .id _ | .tuple _ | .list _ | .proj _ _
  | .ite _ _ _ | .call _ _ | .unop _ _| .binop _ _ _ | .compare _ _ _
  | .defined _ | .undefined _ =>
    throw s!"invalid expression in a field projection"

/-- Check a tuple's components against the product's component types. -/
def checkTuple (Γ : Context) :
    List Input.Expr → (ts : List Ty) → Result { es' : List Expr // TupleOfTy Γ es' ts }
  | [], [] => .ok ⟨[], .nil⟩

  | e :: es, t :: ts => do
    let ⟨e', he⟩ ← check Γ e t
    let ⟨es', hes⟩ ← checkTuple Γ es ts
    return ⟨e' :: es', .cons he hes⟩

  | [], _ :: _ | _ :: _, [] => throw "tuple has the wrong number of components"

/-- Infer types for a tuple's components. -/
def inferTuple (Γ : Context) :
    List Input.Expr → Result (Σ ts : List Ty, { es' : List Expr // TupleOfTy Γ es' ts })

  | [] =>
    .ok ⟨[], [], .nil⟩

  | e :: es => do
    let ⟨t, e', he⟩ ← infer Γ e
    let ⟨ts, es', hes⟩ ← inferTuple Γ es
    return ⟨t :: ts, e' :: es', .cons he hes⟩

/-- Check each list element against `t`. -/
def checkList (Γ : Context) (t : Ty) :
    List Input.Expr → Result { es : List Expr // ListOfTy Γ es t }

  | [] =>
    .ok ⟨[], .nil⟩

  | e :: es => do
    let ⟨e, he⟩ ← check Γ e t
    let ⟨es, hes⟩ ← checkList Γ t es
    return ⟨e :: es, .cons he hes⟩

end

/-- Check each output field in `Γ`, the context of the domain variables. The column names
are distinct from one another. -/
def checkOutput (Γ : Context) :
    List (String × Input.Expr) → Result (List (Ident × Ty × Expr))
  | [] => return []
  | (x', e) :: xes => do
    let ⟨t, e, _⟩ ← infer Γ e
    let rest ← checkOutput Γ xes
    if rest.any (fun (y, _, _) => y == .ident x') then
      throw s!"duplicate output column {x'}"
    return (.ident x', t, e) :: rest

/-- Check the domain bindings, accumulating them in `acc`. The variables are distinct. -/
def checkDomainVars (Γ : Context) (acc : List (Ident × DomainName)) :
    List (String × String) → Result (Context × List (Ident × DomainName))
| [] => return (Γ, acc.reverse)
| (x', n') :: xns => do
  let x := .ident x'
  let n := .domain n'
  if acc.any (fun (y, _) => y == x) then
    throw s!"duplicate domain variable {x'}"
  match Γ.domain.lookup n with
  | .none => throw s!"unknown domain {n'}"
  | .some _ => checkDomainVars (Γ.extendDomainIdent x n) ((x, n) :: acc) xns

def checkOrder (Γ : Context) :
    List Input.OrderEntry → Result (List (Expr × Direction))
  | [] => return []
  | entry :: rest => do
    let ⟨_, e, _⟩ ← infer Γ entry.expr
    let rest ← checkOrder Γ rest
    return (e, entry.dir) :: rest

def checkPostprocess (Γ : Context) :
  List (String × Input.Expr) → Result (List (Ident × Ty × Expr))
| [] => return []
| (x, e) :: ps => do
  let x := .ident x
  match Γ.ident.lookup x with
  | none =>
    let ⟨t, e, _⟩ ← infer Γ e
    let ps ← checkPostprocess (Γ.extendIdent x t) ps
    return (x, t, e) :: ps
  | some _ => throw s!"duplicate field {x} in postprocess"

def checkQuery
  (D : Database)
  (q : Input.Query) : Result Query := do
  let ⟨Γ, vars⟩ ← checkDomainVars D.getSqlContext [] (q.domains.map fun b => (b.var, b.domain))
  let ⟨condition, _⟩ ← check Γ (q.condition.getD (.bool true)) .bool
  let output ← checkOutput Γ q.output
  let order ← checkOrder (Γ.extendOutput output) (q.order.getD [])
  let postprocess ← checkPostprocess (D.getPostContext.extendOutput output) q.postprocess
  return { vars, condition, output, limit := q.limit, order, postprocess }

end MathQL
