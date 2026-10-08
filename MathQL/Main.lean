import MathQL.GraphsSmallDB
import MathQL.SymObSmallDB
import MathQL
import MathQL.Backend.SQLite
import MathQL.Backend.Postgres

/-! The `mathql` executable: a persistent process answering queries over stdin/stdout.

It opens the database once, then reads one JSON request per line and writes one
JSON response per line: `{"rows": …}` on success, `{"error": …}` on failure. This
is the transport the MCP server (`python/src/mathql_mcp`) speaks to. -/

open MathQL

/-- Execute a checked query using the selected database backend. -/
abbrev QueryRunner := Query → IO (Except String Lean.Json)

/-- Run one request `Json` and produce its response `Json`. -/
def handle (database : Database) (runQuery : QueryRunner)
    (j : Lean.Json) : IO Lean.Json := do
  match j.getObjVal? "describe" with
  | .ok _ => return database.describe
  | .error _ =>
    match Input.Query.fromJson j >>= checkQuery database with
    | .error e => return Lean.Json.mkObj [("error", Lean.Json.str e)]
    | .ok q =>
      match ← runQuery q with
      | .error e => return Lean.Json.mkObj [("error", Lean.Json.str e)]
      | .ok rows => return Lean.Json.mkObj [("rows", rows)]

/-- Read requests line by line until end of input, answering each on its own line. -/
partial def loop (database : Database) (runQuery : QueryRunner) :
    IO Unit := do
  let stdin ← IO.getStdin
  let line ← stdin.getLine
  if line.isEmpty then
    pure ()                                   -- end of input
  else
    let request := line.trimAscii.toString
    if request.isEmpty then
      loop database runQuery                   -- blank line, skip
    else
      let response ← match Lean.Json.parse request with
        | .error e => pure (Lean.Json.mkObj [("error", Lean.Json.str s!"invalid JSON: {e}")])
        | .ok j => handle database runQuery j
      let stdout ← IO.getStdout
      stdout.putStrLn response.compress
      stdout.flush
      loop database runQuery

/-- The known databases: each name with its `Database` and its default file path. -/
def databases : List (String × Database × String) :=
  [ ("graphs-small", GraphsSmallDB.database, "../data/graphs-small.db"),
    ("sym-ob-small", SymObSmallDB.database, "../data/sym-ob-small.db") ]

/-- The backend and connection target selected by the command-line arguments. -/
inductive Backend where
  | sqlite (path : String)
  | postgresql (conninfo : String)

/-- An omitted backend retains the original `mathql [database] [path]` interface. -/
def parseBackend (defaultPath : String) : List String → Except String Backend
  | [] => .ok (.sqlite defaultPath)
  | ["--sqlite"] => .ok (.sqlite defaultPath)
  | ["--sqlite", path] => .ok (.sqlite path)
  | ["--postgresql"] => .ok (.postgresql "")
  | ["--postgresql", conninfo] => .ok (.postgresql conninfo)
  | [path] => .ok (.sqlite path)
  | _ => .error "usage: mathql [database] [--sqlite [path] | --postgresql [conninfo] | path]"

/-- Select a database and backend. SQLite remains the default. -/
def main (args : List String) : IO Unit := do
  let (name, backendArgs) := match args with
    | [] => ("graphs-small", [])
    | "--sqlite" :: _ | "--postgresql" :: _ => ("graphs-small", args)
    | name :: rest => (name, rest)
  match databases.find? (fun (n, _, _) => n == name) with
  | none =>
    IO.eprintln s!"unknown database '{name}'; available: \
      {", ".intercalate (databases.map (·.1))}"
  | some (_, database, defaultPath) =>
    match parseBackend defaultPath backendArgs with
    | .error message => IO.eprintln message
    | .ok backend =>
      let db ← match backend with
        | .sqlite path => openSQLiteConnection path
        | .postgresql conninfo => openPostgresConnection conninfo name
      let isSafeAlias ← db.safeAliasPredicate database
      loop database (run db database isSafeAlias)
