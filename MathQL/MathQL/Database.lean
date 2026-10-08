import MathQL.Name
import MathQL.Ty
import MathQL.Context
import MathQL.SQLExpr
import Lean.Data.Json.Basic

namespace MathQL

structure Column where
  /-- The column in the table -/
  column : String
  /-- The field's type in the query language -/
  ty : Ty
  /-- Does this column participate in the primary key? -/
  isPrimary : Bool
  /-- A human description of the field's meaning -/
  doc : String

structure ForeignKey where
  /-- Which domain the foreign key refers to -/
  domain : DomainName
  /-- Matching columns to the ones in the foreign domain -/
  column : List (String × String)
  /-- A human description of the foreign key -/
  doc : String

structure Schema where
  /-- The table/view in the database this domain refers to -/
  table : String
  /-- Mapping from query language fields to columns in the table -/
  column : List (Label × Column)
  /-- Foreign keys -/
  foreignKey : List (Label × ForeignKey)
  /-- A human description of the domain -/
  doc : String

/-- Backend names for a registered MathQL SQL function. Missing PostgreSQL
    support is explicit; SQLite remains the existing default. -/
structure SQLFunctionNames where
  sqlite : String
  postgresql : Option String := none

def SQLFunctionNames.forDialect (names : SQLFunctionNames) (dialect : SQL.Dialect) : Option String :=
  match dialect with
  | .sqlite => some names.sqlite
  | .postgresql => names.postgresql

def Schema.primaryColumns (sch : Schema) : List String :=
  (sch.column.filter (fun (_, c) => c.isPrimary)).map (fun (_, c) => c.column)

def Schema.getForeignKey (sch : Schema) (l : Label): Result ForeignKey :=
  match sch.foreignKey.lookup l with
  | .some fk => return fk
  | .none => throw s!"unknown foreign key {l}"

structure Database where
  /-- A human overview of what the database contains -/
  overview : String
  /-- The constants known to this database -/
  const : List (Ident × Ty × SQL.Expr)
  /-- The domains/tables known to this database -/
  domain : List (DomainName × Schema)
  /-- Typed MathQL names and their backend SQL function names. -/
  sqlFunction : List (Ident × (List Ty × Ty) × SQLFunctionNames)
  /-- Postprocessing functions -/
  postFunction : List (Ident × (List Ty × Ty) × (List Lean.Json → Result Lean.Json))
  /-- Example queries, each with a short note -/
  examples : List (String × Lean.Json)

def Database.getDomainContext (D : Database) : DomainContext :=
  D.domain.map fun (n, d) =>
    (n, { inputField := d.column.map fun (l, f) => (l, {ty := f.ty, isPrimary := f.isPrimary})
          domainField := d.foreignKey.map fun (l, fk) => (l, fk.domain) })

/-- The context for typechecking the query -/
def Database.getSqlContext (D : Database) : Context where
  domain := D.getDomainContext
  function := D.sqlFunction.map fun (x, t, _) => (x, t)
  ident := D.const.map fun (x, t, _) => (x, .ty t)

/-- The context for typechecking postprocessing -/
def Database.getPostContext (D : Database) : Context where
  domain := []
  function := D.postFunction.map (fun ⟨f, t, _⟩ => (f, t))
  ident := []


/-- A JSON description of the database for the `describe` request: an overview, each
domain with its doc and its queryable fields (label, type, doc),
the constants, and example queries. -/
def Database.describe (D : Database) : Lean.Json :=
  let domains := D.domain.map fun (n, dom) =>
    Lean.Json.mkObj
      [ ("name", Lean.Json.str n.name),
        ("doc", Lean.Json.str dom.doc),
        ("inputFields", Lean.Json.arr <| (dom.column.map fun (l, f) =>
          Lean.Json.mkObj
            [ ("label", Lean.Json.str l.name),
              ("type", Lean.Json.str f.ty.render),
              ("doc", Lean.Json.str f.doc) ]).toArray),
        ("domainFields", Lean.Json.arr <| (dom.foreignKey.map fun (l, f) =>
          Lean.Json.mkObj
            [ ("label", Lean.Json.str l.name),
              ("domain", Lean.Json.str f.domain.name),
              ("doc", Lean.Json.str f.doc) ]).toArray) ]
  let constants := D.const.map fun (x, t, _) =>
    Lean.Json.mkObj [("name", Lean.Json.str x.name), ("type", Lean.Json.str t.render)]
  let examples := D.examples.map fun (note, q) =>
    Lean.Json.mkObj [("note", Lean.Json.str note), ("query", q)]
  Lean.Json.mkObj
    [ ("overview", Lean.Json.str D.overview),
      ("domains", Lean.Json.arr domains.toArray),
      ("constants", Lean.Json.arr constants.toArray),
      ("examples", Lean.Json.arr examples.toArray) ]

end MathQL
