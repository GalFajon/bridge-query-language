import MathQL.SQLExpr

namespace MathQL.SQL

/-- A SQL `SELECT` query: the `FROM` tables with their aliases, the hoisted
joins (each a table, its alias, and the columnwise equalities `alias.column =
expr` that form the `ON` condition), the output columns each with its alias, the
boolean condition, the ordering, and the limit. -/
structure Query where
  froms : List (String × String)
  joins : List (String × String × List (String × Expr))
  output : List (Expr × String)
  cond : Expr
  order : List (Expr × Direction)
  limit : Option Nat

/-- Render a query for the selected SQL dialect. Each output column is
rendered as `<expr> AS <alias>`; a hoisted join renders as `LEFT JOIN`, so its
columns are NULL wherever the match is empty.

A query selecting no column renders `SELECT 1`, a query over no table renders
without a `FROM` clause, and a hoisted join over no table renders with
`(SELECT 1)`, a source of one row, to its left. -/
def renderQueryWith (dialect : Dialect) (q : Query) : String :=
  let joins := String.join <| q.joins.map fun ((table, alias, eqs) :
      String × String × List (String × Expr)) =>
    let conds := eqs.map fun (col, e) =>
      s!"{alias}.{renderIdent col} = {renderExprWith dialect e}"
    let on := if conds.isEmpty then renderExprWith dialect (.bool true) else " AND ".intercalate conds
    s!" LEFT JOIN {renderIdent table} AS {alias} ON {on}"
  let from_ := match q.froms with
    | [] => if q.joins.isEmpty then "" else
        match dialect with
        | .sqlite => " FROM (SELECT 1)"
        | .postgresql => " FROM (SELECT 1) AS _mathql_seed"
    | froms =>
      -- A PostgreSQL JOIN's ON clause must see all preceding domain variables.
      let sep := if dialect == Dialect.postgresql then " CROSS JOIN " else ", "
      " FROM " ++ sep.intercalate (froms.map fun ((table, alias) : String × String) =>
        s!"{renderIdent table} AS {alias}")
  let cols := match q.output with
    | [] => "1"
    | output => ", ".intercalate (output.map fun ((e, alias) : Expr × String) =>
        s!"{renderExprWith dialect e} AS {alias}")
  let order := match q.order with
    | [] => ""
    | es => " ORDER BY " ++ ", ".intercalate (es.map fun ((e, d) : Expr × Direction) =>
        let nulls := match dialect, d with
          | .postgresql, .asc => " NULLS FIRST"
          | .postgresql, .desc => " NULLS LAST"
          | .sqlite, _ => ""
        s!"{renderExprWith dialect e} {renderDir d}{nulls}")
  let limit := match q.limit with | some n => s!" LIMIT {n}" | none => ""
  s!"SELECT {cols}{from_}{joins} WHERE {renderExprWith dialect q.cond}{order}{limit}"

/-- SQLite remains the default for existing callers. -/
def renderQuery (q : Query) : String := renderQueryWith .sqlite q

instance : ToString Expr  := ⟨renderExpr⟩
instance : ToString Query := ⟨renderQuery⟩

end MathQL.SQL
