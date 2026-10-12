import MathQL
import MathQL.Backend.SQLite
import MathQL.Backend.Postgres

open MathQL

private def col (name : String) (ty : Ty) : Label × Column :=
  (.label name, { column := name, ty, isPrimary := name == "id", doc := "" })

private def fixture : Database where
  overview := "backend conformance fixture"
  const := []
  domain := [(.domain "Row", {
    table := "mathql_backend_test"
    column := [col "id" .int, col "n" .int, col "flag" .bool, col "label" .string,
      col "pair" (.prod [.int, .bool, .string, .list .int, .list .bool]),
      col "items" (.list .int), col "bad" (.list .int)]
    foreignKey := [(.label "parent", {
      domain := .domain "Row", column := [("ref", "id")], doc := "" })]
    doc := "" })]
  sqlFunction := []
  postFunction := []
  examples := []

private def entries (xs : List (String × String)) : Lean.Json :=
  Lean.toJson (xs.map fun (a, b) => [a, b])

private def query (output : List (String × String)) (condition := "true")
    (order : List (String × String) := []) (post : List (String × String) := [])
    (withDomain := true) : Lean.Json :=
  Lean.Json.mkObj [
    ("domains", if withDomain then json% [["r", "Row"]] else json% []),
    ("output", entries output), ("condition", .str condition),
    ("order", entries order), ("postprocess", entries post)]

private def check (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

private def execute (db : Connection) (sql : String) : IO Unit := do
  let cursor ← db.prepare sql
  discard cursor.next

/-- Both fixtures have identical logical values; only their physical SQL types differ. -/
private def setup (db : Connection) : IO Unit := do
  let jsonTy := if db.dialect == .postgresql then "JSONB" else "TEXT"
  execute db s!"CREATE TEMP TABLE mathql_backend_test (id BIGINT PRIMARY KEY, \
    n BIGINT, flag BOOLEAN, label TEXT, pair {jsonTy}, items {jsonTy}, \
    ref BIGINT, bad TEXT, c1 BIGINT, \"C2\" BIGINT)"
  let str := fun s => SQL.renderExprWith db.dialect (.str s)
  let json := fun s => if db.dialect == .postgresql then s!"{str s}::jsonb" else str s
  let pair1 := json "[7,true,\"O'Brien\\\\path\",[1,2],[true,false]]"
  let pair2 := json "[10,false,\"z\",[],[]]"
  execute db s!"INSERT INTO mathql_backend_test VALUES \
    (1, 2, TRUE, {str "O'Brien\\path"}, {pair1}, {json "[2,10]"}, 99, 'oops', 0, 0), \
    (2, 1, FALSE, 'z', {pair2}, {json "[2,2]"}, 1, 'oops', 0, 0), \
    (3, NULL, NULL, NULL, NULL, {json "[]"}, NULL, 'oops', 0, 0)"

private def checked (j : Lean.Json) : IO Query :=
  match Input.Query.fromJson j >>= checkQuery fixture with
  | .ok q => pure q
  | .error e => throw (IO.userError s!"test query did not typecheck: {e}")

private def expect (db : Connection) (safe : String → Bool) (name : String)
    (j expected : Lean.Json) : IO Unit := do
  let result ← run db fixture safe (← checked j)
  match result with
  | .error e => throw (IO.userError s!"{name}: {e}")
  | .ok actual =>
    check (actual == expected) s!"{name}: expected {expected.compress}, got {actual.compress}"
  IO.println s!"  PASS {name}"

private def suite (db : Connection) : IO Unit := do
  setup db
  let safe ← db.safeAliasPredicate fixture
  check (!safe "c1" && !safe "c2" && safe "c3") "metadata must include undeclared and mixed-case columns"
  IO.println "  PASS alias discovery"
  expect db safe "scalar types, nulls, and escaping"
    (query [("id", "r.id"), ("n", "r.n"), ("b", "r.flag"), ("s", "r.label")]
      "true" [("r.id", "asc")])
    (json% [[["id", 1], ["n", 2], ["b", true], ["s", "O'Brien\\path"]],
            [["id", 2], ["n", 1], ["b", false], ["s", "z"]],
            [["id", 3], ["n", null], ["b", null], ["s", null]]])
  expect db safe "typed tuple projections in arithmetic and conditions"
    (query [("v", "r.pair.0 + 1"), ("s", "r.pair.2"), ("b", "!r.pair.1")]
      "r.pair.0 + 1 == 8 && r.pair.1")
    (json% [[["v", 8], ["s", "O'Brien\\path"], ["b", false]]])
  expect db safe "string literals retain apostrophes, backslashes, and Unicode"
    (query [("s", "'O''Brien\\path λ'")] "true" [] [] false)
    (json% [[["s", "O'Brien\\path λ"]]])
  expect db safe "nested tuple projection and conditional"
    (query [("b", "(r.pair, r.items).0.1"),
      ("v", "if r.flag then r.pair.0 else 0")] "r.id == 1")
    (json% [[["b", true], ["v", 7]]])
  expect db safe "nested JSON arrays and booleans"
    (query [("v", "[r.items, [1,2]]"), ("t", "(r.flag, r.items, r.pair.2)"),
      ("bs", "r.pair.4")] "r.id == 1")
    (json% [[["v", [[2,10],[1,2]]], ["t", [true,[2,10],"O'Brien\\path"]],
      ["bs", [true,false]]]])
  expect db safe "nested booleans remain booleans through postprocessing"
    (query [("flag", "r.flag"), ("tuple", "(r.flag, r.n)"),
      ("list", "[r.flag, false]")] "r.id == 1" []
      [("first", "tuple.0"), ("is_true", "tuple.0 == true")])
    (json% [[["flag", true], ["tuple", [true,2]], ["list", [true,false]],
      ["first", true], ["is_true", true]]])
  expect db safe "JSON null remains undefined after composite projection"
    (query [("v", "(r.items, r.pair).1"), ("missing", "undefined (r.items, r.pair).1")]
      "r.id == 3")
    (json% [[["v", null], ["missing", true]]])
  expect db safe "constructed boolean lists preserve null"
    (query [("bs", "[r.flag, true, false]")] "r.id == 3")
    (json% [[["bs", [null,true,false]]]])
  expect db safe "JSON equality"
    (query [("id", "r.id")] "r.items == [2,10]")
    (json% [[["id", 1]]])
  expect db safe "NULLS FIRST ascending"
    (query [("id", "r.id")] "true" [("r.n", "asc"), ("r.id", "asc")])
    (json% [[["id", 3]], [["id", 2]], [["id", 1]]])
  expect db safe "NULLS LAST descending"
    (query [("id", "r.id")] "true" [("r.n", "desc"), ("r.id", "asc")])
    (json% [[["id", 1]], [["id", 2]], [["id", 3]]])
  expect db safe "left join and missing target"
    (query [("id", "r.id"), ("parent", "r.parent.n")] "true" [("r.id", "asc")])
    (json% [[["id", 1], ["parent", null]], [["id", 2], ["parent", 2]],
      [["id", 3], ["parent", null]]])
  expect db safe "object lookup without FROM variables"
    (query [("n", "Row[1].n")] "true" [] [] false)
    (json% [[["n", 2]]])
  expect db safe "join can refer to the first of multiple domain variables"
    (json% {"domains": [["r", "Row"], ["s", "Row"]],
      "output": [["n", "r.parent.n"]], "condition": "r.id == 2 && s.id == 1"})
    (json% [[["n", 2]]])
  expect db safe "shared postprocessing and dependent fields"
    (query [("n", "r.n")] "r.id == 1" [] [("a", "n + 1"), ("b", "a * 2")])
    (json% [[["n", 2], ["a", 3], ["b", 6]]])
  expect db safe "empty result" (query [("id", "r.id")] "false") (json% [])
  expect db safe "empty output preserves row count" (query [] "r.id <= 2") (json% [[],[]])
  expect db safe "64-bit literal arithmetic"
    (query [("n", "2147483647 + 1")] "true" [] [] false)
    (json% [[["n", 2147483648]]])
  expect db safe "division truncates toward zero in SQL and postprocessing"
    (query [("positive", "7 / 2"), ("negative", "-7 / 2"),
      ("opposite", "7 / -2"), ("mixed", "2 * 6 / 4")]
      "true" [] [("post", "negative / 2"), ("post_mixed", "mixed / 2")] false)
    (json% [[["positive", 3], ["negative", -3], ["opposite", -3],
      ["mixed", 3], ["post", -1], ["post_mixed", 1]]])
  expect db safe "division by zero is absent in both stages"
    (query [("zero", "7 / 0")] "true" []
      [("post_zero", "7 / 0"), ("undefined_sql", "undefined zero"),
       ("undefined_post", "undefined post_zero")] false)
    (json% [[["zero", null], ["post_zero", null], ["undefined_sql", true],
      ["undefined_post", true]]])
  expect db safe "signed 64-bit boundaries"
    (query [("lo", "-9223372036854775808"), ("hi", "9223372036854775807")]
      "true" [] [] false)
    (json% [[["lo", -9223372036854775808], ["hi", 9223372036854775807]]])
  expect db safe "limit and ordering by output alias"
    (json% {"domains": [["r", "Row"]], "output": [["n", "r.n"]],
      "condition": "true", "order": [["n", "desc"]], "limit": 1})
    (json% [[["n", 2]]])
  -- This existing language behavior is native: SQLite compares JSON text;
  -- PostgreSQL compares JSONB structurally. Keep the difference explicit.
  expect db safe "native JSON ordering"
    (query [("b", "[2,2] > [2,10]")] "true" [] [] false)
    (if db.dialect == .sqlite then json% [[["b", true]]] else json% [[["b", false]]])
  let bad ← run db fixture safe (← checked (query [("bad", "r.bad")] "r.id == 1"))
  check bad.toOption.isNone "invalid JSON must return an error"
  let missing := { fixture with domain := fixture.domain.map fun (n, sch) =>
    (n, { sch with table := "mathql_backend_missing_table" }) }
  let failed ← run db missing safe (← checked (query [("id", "r.id")]))
  check failed.toOption.isNone "driver failures must return an error"
  let failedCompile ← run db fixture (fun _ => false) (← checked (query [("id", "r.id")]))
  check failedCompile.toOption.isNone "compilation failures must return an error"
  IO.println "  PASS decoding, driver, and compilation errors"
  expect db safe "connection remains usable after an error"
    (query [("id", "r.id")] "r.id == 2") (json% [[["id", 2]]])

/-- PostgreSQL is opt-in, but a supplied connection must work: errors never become skips. -/
def main : IO Unit := do
  IO.println "SQLite"
  suite (sqliteConnection (← SQLite.«open» ":memory:"))
  match ← IO.getEnv "MATHQL_TEST_POSTGRES" with
  | none => IO.println "SKIP PostgreSQL: set MATHQL_TEST_POSTGRES to a libpq connection string"
  | some conninfo =>
    IO.println "PostgreSQL"
    suite (postgresConnection (← Postgres.«open» conninfo))
