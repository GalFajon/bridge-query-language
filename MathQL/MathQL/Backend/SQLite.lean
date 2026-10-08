import MathQL.Backend
import SQLite

namespace MathQL

private def readSQLiteCell (stmt : SQLite.Stmt) (index : Nat) (ty : Ty) : IO Lean.Json := do
  let i := Int32.ofInt index
  if (← stmt.columnType i) == .null then return .null
  match ty with
  | .int => return Lean.toJson (← stmt.columnInt64 i).toInt
  | .bool => return Lean.toJson ((← stmt.columnInt64 i) != 0)
  | .string => return .str (← stmt.columnText i)
  | .list _ | .prod _ => parseJsonCell (← stmt.columnText i)

/-- Adapt an open SQLite connection; the captured statements retain their connection. -/
def sqliteConnection (db : SQLite) : Connection where
  dialect := .sqlite
  prepare sql := do
    let stmt ← db.prepare sql
    return { next := stmt.step, readCell := readSQLiteCell stmt }
  columnNames table := do
    let stmt ← db.prepare "SELECT name FROM pragma_table_xinfo(?)"
    stmt.bindText 1 table
    return (← (stmt.resultsAs String).toArray).toList
  reservedNames := ["rowid", "oid", "_rowid_"]

/-- Open the executable's SQLite database read-only. -/
def openSQLiteConnection (path : String) : IO Connection := do
  return sqliteConnection (← SQLite.openWith path .readonly)

end MathQL
