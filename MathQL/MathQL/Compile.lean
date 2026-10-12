import MathQL.Name
import MathQL.Expr
import MathQL.Result
import MathQL.SQL
import MathQL.Database
import MathQL.Query
import MathQL.Integer

/-! Compilation of a type-checked query to SQL: scalar expressions compile to SQL
expressions, and domain expressions compile to aliased table rows, hoisted into
shared `LEFT JOIN`s. -/

namespace MathQL

/-- an alias in an SQL query -/
inductive Alias where
  | alias : String → Alias

abbrev Alias.name : Alias → String
  | .alias s => s

/-- The compilation entry of an identifier: a domain variable with its domain,
    or a constant with its SQL literal. -/
inductive ContextEntry where
  | domain : DomainName → ContextEntry
  | const : SQL.Expr → ContextEntry

/-- The resolution context of a compilation. -/
structure SqlCtx where
  /-- The entry of each identifier; earlier entries shadow later ones. -/
  ident : List (Ident × ContextEntry)
  /-- The schema of a domain. -/
  schema : List (DomainName × Schema)
  /-- The mapping from MathQL function names to SQL functions -/
  function : List (Ident × SQLFunctionNames)
  dialect : SQL.Dialect
  /-- Is a name free of the column names of the database, and so usable as an alias? -/
  isSafeAlias : String → Bool

/-- The state of a compilation: the next alias to try, the alias of each domain
    variable, the hoisted joins (table, alias, `ON` condition), and the mapping
    from hoisted domain expressions to their alias and domain. -/
structure CompileState where
  /-- The index of the next candidate alias -/
  nextAlias : Nat
  /-- The table alias of each domain variable -/
  varAlias : List (Ident × Alias)
  /-- Current left joins -/
  joins : List (String × Alias × List (String × SQL.Expr))
  /-- Domains that have so far been hoisted to left joins -/
  hoisted : List (Domain × (Alias × DomainName))

abbrev CompileM := StateT CompileState Result

def SqlCtx.getIdent (Γ : SqlCtx) (x : Ident) : CompileM ContextEntry :=
  match Γ.ident.lookup x with
  | some ce => return ce
  | none => throw s!"unknown identifier {x}"

def SqlCtx.getSchema (Γ : SqlCtx) (dn : DomainName) : CompileM Schema :=
  match Γ.schema.lookup dn with
  | none => throw s!"unknown domain name {dn}"
  | some sch => return sch

def SqlCtx.getColumn (Γ : SqlCtx) (dn : DomainName) (l : Label) : CompileM Column := do
  let sch ← Γ.getSchema dn
  match sch.column.lookup l with
  | some c => return c
  | none => throw s!"unknown column {l} in schema {dn}"

def lookupHoist (d : Domain) : CompileM (Option (Alias × DomainName)) := do
  let st ← get
  return st.hoisted.lookup d

def storeHoist (d : Domain) (a : Alias) (dn : DomainName): CompileM Unit := do
  modify fun st => { st with hoisted := (d, (a, dn)) :: st.hoisted }

def lookupVarAlias (x : Ident) : CompileM (Option Alias) := do
  let st ← get
  return st.varAlias.lookup x

def storeVarAlias (x : Ident) (a : Alias) : CompileM Unit := do
  modify fun st => { st with varAlias := (x, a) :: st.varAlias }

/-- How many candidates `firstSafe` tries before it gives up. -/
private def aliasFuel : Nat := 1000

/-- The first of `cₙ`, `cₙ₊₁`, … that `isSafeAlias` accepts, with its index. -/
private def firstSafe (isSafeAlias : String → Bool) (n : Nat) : Nat → Option (String × Nat)
  | 0 => none
  | fuel + 1 =>
    let cand := s!"c{n}"
    if isSafeAlias cand then some (cand, n) else firstSafe isSafeAlias (n + 1) fuel

/-- A fresh alias that `Γ.isSafeAlias` accepts. -/
def freshSafeAlias (Γ : SqlCtx) : CompileM Alias := do
  let st ← get
  match firstSafe Γ.isSafeAlias st.nextAlias aliasFuel with
  | some (name, n) =>
    modify fun st => { st with nextAlias := n + 1 }
    return .alias name
  | none => throw "internal error: no safe alias available"

def getPrimaryKey (Γ : SqlCtx) (dn : DomainName) : CompileM (List Column) := do
  let sch ← Γ.getSchema dn
  return (sch.column.map Prod.snd).filter Column.isPrimary

def mkJoin (Γ : SqlCtx) (table : String) (eqs : List (String × SQL.Expr))
  : CompileM Alias
  := do
  let alias ← freshSafeAlias Γ
  modify (fun st => { st with joins := (table, alias, eqs) :: st.joins })
  return alias

mutual

/-- The alias of the row denoted by a domain expression, and its domain. The
    result for an equal expression is stored and reused. A domain variable
    resolves to the alias allocated for its binding; an `obj` or a domain-valued
    field is hoisted to a join. -/
def compileDomain (Γ : SqlCtx) (d : Domain) : CompileM (Alias × DomainName) := do
  match d with

  | .ident x => do
    let ce ← Γ.getIdent x
    match ce with
    | .domain d =>
      match (← lookupVarAlias x) with
      | some a => return (a, d)
      | none => throw s!"unbound domain variable {x}"
    | .const _  => throw s!"{x} is not a domain variable"

  | .obj dn es =>
    match (← lookupHoist d) with
    | some r => return r
    | none =>
      let sch ← Γ.getSchema dn
      let ks ← compileExprList Γ es
      let a ← mkJoin Γ sch.table (List.zip sch.primaryColumns ks)
      storeHoist d a dn
      return (a, dn)

  | .field d' l =>
    match (← lookupHoist d) with
    | some r => return r
    | none =>
      let (a', dn) ← compileDomain Γ d'
      let sch ← Γ.getSchema dn
      let f ← sch.getForeignKey l
      let fsch ← Γ.getSchema f.domain
      let eqs := f.column.map (fun (c, c') => (c', .col a'.name c))
      let a ← mkJoin Γ fsch.table eqs
      storeHoist d a f.domain
      return (a, f.domain)

termination_by sizeOf d

/-- Compile a scalar expression to a SQL expression. -/
def compileExpr (Γ : SqlCtx) (e : Expr) : CompileM SQL.Expr := do
  match e with
  | .int n => return .int (← checkedInteger n)

  | .bool b => return .bool b

  | .str s => return .str s

  | .ident x =>
    match Γ.ident.lookup x with
    | some (.const s) => return s
    | some (.domain _) => throw s!"{x} is a domain variable, not a value"
    | none => throw s!"unknown constant {x}"

  | .id d =>
    let (alias, dn) ← compileDomain Γ d
    let sch ← Γ.getSchema dn
    return .jsonArray' (sch.primaryColumns.map (fun c => .col alias.name c))

  | .field d l =>
    let (alias, dn) ← compileDomain Γ d
    let f ← Γ.getColumn dn l
    return .col alias.name f.column

  | .call f es =>
    let ss ← compileExprList Γ es
    match Γ.function.lookup f with
    | .none => throw s!"unknown function {f.name}"
    | .some names =>
      match names.forDialect Γ.dialect with
      | .some c => return .call c ss
      | .none => throw s!"function {f.name} is not available on PostgreSQL"

  -- The minimum signed integer is parsed as negation of a positive literal.
  | .unop .neg (.int n) => return .int (← checkedInteger (-n))

  | .unop op e =>
    let s ← compileExpr Γ e
    return .unop op s

  | .binop op e₁ e₂ =>
    let s₁ ← compileExpr Γ e₁
    let s₂ ← compileExpr Γ e₂
    return .binop op s₁ s₂

  | .compare op t e₁ e₂ =>
    let s₁ ← compileExpr Γ e₁
    let s₂ ← compileExpr Γ e₂
    match t with
    | .list _ | .prod _ => return .compare op (.json s₁) (.json s₂)
    | .int | .bool | .string => return .compare op s₁ s₂

  | .ite c a b =>
    let sc ← compileExpr Γ c
    let sa ← compileExpr Γ a
    let sb ← compileExpr Γ b
    return .case sc sa sb

  | .defined (.id d) =>
    let (alias, dn) ← compileDomain Γ d
    let sch ← Γ.getSchema dn
    let pks := sch.primaryColumns
    match pks with
    | [] => return .bool true
    | c :: _ => return .isNotNull (.col alias.name c)

  | .defined e =>
      let s ← compileExpr Γ e
      return .isNotNull s

  | .undefined (.id d)=>
    let (alias, dn) ← compileDomain Γ d
    let sch ← Γ.getSchema dn
    let pks := sch.primaryColumns
    match pks with
    | [] => return .bool true
    | c :: _ => return .isNull (.col alias.name c)

  | .undefined e =>
      let s ← compileExpr Γ e
      return .isNull s

  | .tuple ts es =>
    let ss ← compileExprList Γ es
    return .jsonArray ((ts.zip ss).map fun (t, s) => .jsonValue t s)

  | .list t es =>
    let ss ← compileExprList Γ es
    return .jsonArray (ss.map (.jsonValue t))

  | .proj t e i =>
    let s ← compileExpr Γ e
    return .jsonExtract t s i

termination_by sizeOf e

/-- Compile a list of expressions for a `json_array` argument list. -/
def compileExprList (Γ : SqlCtx) : List Expr → CompileM (List SQL.Expr)
  | [] => return []
  | e :: es => do
    let s ← compileExpr Γ e
    let ss ← compileExprList Γ es
    return s :: ss
termination_by es => sizeOf es

end

/-- Compile a type-checked query to a SQL query, with `isSafeAlias` deciding which
    names may serve as aliases. -/
def compileQueryWith (dialect : SQL.Dialect) (D : Database)
    (isSafeAlias : String → Bool) (q : Query) :
    Result SQL.Query := do
  let Γ : SqlCtx :=
    { ident := (q.vars.map fun (x, n) => (x, .domain n)) ++
               (D.const.map fun (x, _, s) => (x, .const s))
      function := D.sqlFunction.map (fun ⟨f, _, c⟩ => (f ,c))
      dialect := dialect
      schema := D.domain
      isSafeAlias := isSafeAlias
    }
  let act : CompileM (List (String × String) × List (SQL.Expr × String) ×
                      SQL.Expr × List (SQL.Expr × Direction)) := do
    let froms ← q.vars.mapM fun (x, n) =>
      match D.domain.lookup n with
      | some dom => do
        let a ← freshSafeAlias Γ
        storeVarAlias x a
        return (dom.table, a.name)
      | none => throw s!"unknown domain {n}"
    let columns ← q.output.mapM fun (x, _, e) => do
      let a ← freshSafeAlias Γ
      let s ← compileExpr Γ e
      return (x, a.name, s)
    let output := columns.map fun (_, a, s) => (s, a)
    let Δ : SqlCtx :=
      { Γ with ident := (columns.map fun (x, a, _) => (x, .const (.ref a))) ++ Γ.ident }
    let cond ← compileExpr Γ q.condition
    let order ← q.order.filterMapM fun ((e, dir) : Expr × Direction) => do
      let s ← compileExpr Δ e
      return if s.isConstant then none else some (s, dir)
    return (froms, output, cond, order)
  match act.run { nextAlias := 1, varAlias := [], joins := [], hoisted := [] } with
  | .error e => throw e
  | .ok ((froms, output, cond, order), st) =>
    let joins := st.joins.reverse.map fun (table, alias, eqs) => (table, alias.name, eqs)
    return { froms, joins, output, cond, order, limit := q.limit }

/-- Preserve the original SQLite compilation entry point for existing callers. -/
def compileQuery (D : Database) (isSafeAlias : String → Bool) (q : Query) :
    Result SQL.Query := compileQueryWith .sqlite D isSafeAlias q

end MathQL
