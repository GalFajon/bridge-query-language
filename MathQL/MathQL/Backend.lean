import MathQL.Database
import Lean.Data.Json

namespace MathQL

/-- A cursor positioned by `next`; column indices are zero-based. -/
structure Cursor where
  next : IO Bool
  readCell : Nat → Ty → IO Lean.Json

/-- The database operations needed by the shared query executor. -/
structure Connection where
  dialect : SQL.Dialect
  prepare : String → IO Cursor
  columnNames : String → IO (List String)
  reservedNames : List String := []

/-- Discover all physical column names, including fields absent from the descriptor. -/
def Connection.safeAliasPredicate (db : Connection) (D : Database) :
    IO (String → Bool) := do
  let columns ← D.domain.mapM fun (_, sch) => db.columnNames sch.table
  let taken := (db.reservedNames ++ columns.flatten).map String.toLower
  return fun s => !taken.contains s.toLower

/-- Decode the JSON representation shared by list and product columns. -/
def parseJsonCell (s : String) : IO Lean.Json :=
  match Lean.Json.parse s with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"expected JSON in a list or product column: {e}")

end MathQL
