import MathQL.Backend
import Postgres

namespace MathQL

private def readPostgresCell (stmt : Postgres.Stmt) (index : Nat) (ty : Ty) : IO Lean.Json := do
  let i := Int32.ofInt index
  if ← stmt.columnIsNull i then return .null
  match ty with
  | .int => return Lean.toJson (← stmt.columnInt64 i).toInt
  | .bool => return Lean.toJson (← Postgres.ResultColumn.get (α := Bool) stmt i)
  | .string => return .str (← stmt.columnText i)
  | .list _ | .prod _ => parseJsonCell (← stmt.columnText i)

/-- Resolve metadata through the same search path used by generated queries. -/
def postgresConnection (db : Postgres.Conn) : Connection where
  dialect := .postgresql
  prepare sql := do
    let stmt ← Postgres.prepare db sql
    return { next := stmt.step, readCell := readPostgresCell stmt }
  columnNames table := do
    let stmt ← Postgres.prepare db
      "SELECT attname FROM pg_catalog.pg_attribute \
       WHERE attrelid = pg_catalog.to_regclass($1) AND NOT attisdropped"
    stmt.bindText 1 (SQL.renderIdent table)
    return (← (stmt.resultsAs String).toArray).toList

/-- Open PostgreSQL and select the schema named by the MathQL database. -/
def openPostgresConnection (conninfo schema : String) : IO Connection := do
  let db ← Postgres.«open» conninfo
  let check ← Postgres.prepare db
    "SELECT 1 FROM pg_catalog.pg_namespace WHERE nspname = $1"
  check.bindText 1 schema
  unless ← check.step do
    throw <| IO.userError s!"PostgreSQL schema '{schema}' does not exist"
  Postgres.execScript db s!"SET search_path TO {SQL.renderIdent schema}"
  return postgresConnection db

end MathQL
