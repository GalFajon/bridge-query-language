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
      col "items" (.list .int), col "bad" (.list .int), col "narrow" .int]
    foreignKey := [(.label "parent", {
      domain := .domain "Row", column := [("ref", "id")], doc := "" })]
    doc := "" }),
    (.domain "TextRow", {
      table := "mathql_backend_test"
      column := [(.label "label", {column := "label", ty := .string, isPrimary := true, doc := ""}),
        col "n" .int]
      foreignKey := []
      doc := "string-key collation fixture" })]
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
  let labelTy := if db.dialect == .sqlite then "TEXT COLLATE NOCASE" else "TEXT"
  execute db s!"CREATE TEMP TABLE mathql_backend_test (id BIGINT PRIMARY KEY, \
    n BIGINT, flag BOOLEAN, label {labelTy}, pair {jsonTy}, items {jsonTy}, \
    ref BIGINT, bad TEXT, c1 BIGINT, \"C2\" BIGINT, narrow INTEGER)"
  let str := fun s => SQL.renderExprWith db.dialect (.str s)
  let json := fun s => if db.dialect == .postgresql then s!"{str s}::jsonb" else str s
  let pair1 := json "[7,true,\"O'Brien\\\\path\",[1,2],[true,false]]"
  let pair2 := json "[10,false,\"z\",[],[]]"
  execute db s!"INSERT INTO mathql_backend_test VALUES \
    (1, 2, TRUE, {str "O'Brien\\path"}, {pair1}, {json "[2,10]"}, 99, 'oops', 0, 0, 2147483647), \
    (2, 1, FALSE, 'z', {pair2}, {json "[2,2]"}, 1, 'oops', 0, 0, -2147483648), \
    (3, NULL, NULL, NULL, NULL, {json "[]"}, NULL, 'oops', 0, 0, NULL)"

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

private def expectOverflow (db : Connection) (safe : String → Bool)
    (name : String) (j : Lean.Json) : IO Unit := do
  match ← run db fixture safe (← checked j) with
  | .ok value => throw <| IO.userError s!"{name}: expected overflow, got {value.compress}"
  | .error message =>
    check (message.contains "overflow" || message.contains "out of range")
      s!"{name}: wrong error: {message}"
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
  for count in [0, 1, 99, 100, 101, 200, 201] do
    let elements := (List.range count).map toString
    let value := Lean.toJson (List.range count)
    -- The conditional supplies the element type for the empty-list case.
    let list := s!"if false then [0] else [{", ".intercalate elements}]"
    expect db safe s!"list constructor with {count} elements"
      (query [("v", list)] "true" [] [] false)
      (Lean.toJson [[("v", value)]])
    if count > 1 then
      expect db safe s!"tuple constructor with {count} elements"
        (query [("v", s!"({", ".intercalate elements})")] "true" [] [] false)
        (Lean.toJson [[("v", value)]])
  let repeated := List.replicate 101 "r.items"
  expect db safe "large nested array preserves array elements"
    (query [("v", s!"[{", ".intercalate repeated}]")] "r.id == 1")
    (Lean.toJson [[("v", Lean.toJson (List.replicate 101 (json% [2,10])))]])
  let bools := List.replicate 100 "true" ++ ["r.flag", "false"]
  expect db safe "large boolean list preserves null at chunk boundary"
    (query [("v", s!"[{", ".intercalate bools}]")] "r.id == 3")
    (Lean.toJson [[("v", Lean.toJson (List.replicate 100 (json% true) ++
      [Lean.Json.null, json% false]))]])
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
  expect db safe "32-bit storage uses 64-bit MathQL arithmetic"
    (query [("sum", "r.narrow + r.narrow"), ("square", "r.narrow * r.narrow"),
      ("neg", "-r.narrow")] "r.id == 2")
    (json% [[["sum", -4294967296], ["square", 4611686018427387904],
      ["neg", 2147483648]]])
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
  -- Exercise all nine pairs, including computed absence rather than only stored NULL.
  let truth := [("true", json% true), ("false", json% false),
    ("(1 / 0 == 0)", Lean.Json.null)]
  let andTable := [[json% true, json% false, Lean.Json.null],
    [json% false, json% false, json% false],
    [Lean.Json.null, json% false, Lean.Json.null]]
  let orTable := [[json% true, json% true, json% true],
    [json% true, json% false, Lean.Json.null],
    [json% true, Lean.Json.null, Lean.Json.null]]
  for ((a, _), i) in truth.zipIdx do
    for ((b, _), k) in truth.zipIdx do
      for (op, table) in [("&&", andTable), ("||", orTable)] do
        let expr := s!"{a} {op} {b}"
        let value := (table[i]!)[k]!
        expect db safe s!"three-valued logic: {expr}"
          (query [("sql", expr)] "true" [] [("post", expr)] false)
          (Lean.toJson [[("sql", value), ("post", value)]])
  for (expr, value) in [
      ("!(1 / 0 == 0)", Lean.Json.null),
      ("- (1 / 0)", Lean.Json.null),
      ("if 1 / 0 == 0 then 1 else 2", json% 2),
      ("(1 / 0, 2)", json% [null, 2]),
      ("[1 / 0, 2]", json% [null, 2]),
      ("([1 / 0, 2], (3, 1 / 0))", json% [[null, 2], [3, null]]),
      ("(1 / 0, 2).1", json% 2),
      ("defined (1 / 0, 2)", json% true),
      ("undefined (1 / 0, 2).0", json% true),
      ("defined [1 / 0, 2]", json% true)] do
    expect db safe s!"compositional absence: {expr}"
      (query [("sql", expr)] "true" [] [("post", expr)] false)
      (Lean.toJson [[("sql", value), ("post", value)]])
  for op in ["+", "-", "*", "/", "==", "!=", "<", "<=", ">", ">="] do
    for expr in [s!"(1 / 0) {op} 2", s!"2 {op} (1 / 0)"] do
      expect db safe s!"null propagation: {expr}"
        (query [("sql", expr)] "true" [] [("post", expr)] false)
        (json% [[["sql", null], ["post", null]]])
  expect db safe "stored null and dependent postprocess absence agree"
    (query [("b", "r.flag"), ("n", "r.n"),
      ("sql_and", "false && r.flag"), ("sql_or", "true || r.flag"),
      ("sql_if", "if r.flag then 1 else 2"), ("sql_tuple", "(r.n, 2)")]
      "r.id == 3" [] [("post_and", "false && b"), ("post_or", "true || b"),
        ("post_if", "if b then 1 else 2"), ("post_tuple", "(n, 2)"),
        ("missing", "1 / 0"), ("dependent", "(missing, 2)")])
    (json% [[["b", null], ["n", null], ["sql_and", false], ["sql_or", true],
      ["sql_if", 2], ["sql_tuple", [null, 2]], ["post_and", false],
      ["post_or", true], ["post_if", 2], ["post_tuple", [null, 2]],
      ["missing", null], ["dependent", [null, 2]]]])
  for expr in ["(1 / 0, 9223372036854775807 + 1)",
      "[1 / 0, 9223372036854775807 + 1]",
      "defined (1 / 0, 9223372036854775807 + 1)"] do
    expectOverflow db safe "absence must not mask a later postprocessing overflow"
      (query [] "true" [] [("v", expr)] false)
  let overflows := ["9223372036854775808", "-9223372036854775809",
    "9223372036854775807 + 1", "-9223372036854775808 - 1",
    "3037000500 * 3037000500", "-(-9223372036854775808)",
    "-9223372036854775808 / -1", "(9223372036854775807 + 1) - 1"]
  for expr in overflows do
    expectOverflow db safe s!"SQL overflow: {expr}"
      (query [("n", expr)] "true" [] [] false)
    expectOverflow db safe s!"postprocessing overflow: {expr}"
      (query [] "true" [] [("n", expr)] false)
  expectOverflow db safe "overflow inside SQL tuple"
    (query [("t", "(r.n + 9223372036854775807, true)")] "r.id == 1")
  expectOverflow db safe "overflow in condition"
    (query [("id", "r.id")] "r.n + 9223372036854775807 > 0")
  expectOverflow db safe "overflow in order key"
    (query [("id", "r.id")] "true" [("r.n + 9223372036854775807", "asc")])
  expectOverflow db safe "defined cannot hide SQL overflow"
    (query [("b", "defined (r.n + 9223372036854775807)")] "r.id == 1")
  for expr in ["defined (9223372036854775807 + 1)",
      "undefined (9223372036854775807 + 1)", "[9223372036854775807 + 1]"] do
    expectOverflow db safe "postprocessing cannot hide overflow"
      (query [] "true" [] [("v", expr)] false)
  expect db safe "in-range arithmetic and SQL nulls"
    (query [("n", "r.n * 2 + 1"), ("zero", "r.n / 0")]
      "true" [("r.id", "asc")])
    (json% [[["n", 5], ["zero", null]], [["n", 3], ["zero", null]],
      [["n", null], ["zero", null]]])
  expect db safe "arithmetic at the signed boundaries remains exact"
    (query [("hi", "9223372036854775806 + 1"),
      ("lo", "-9223372036854775807 - 1"), ("neg", "-(-2)"),
      ("div", "-9223372036854775808 / 1")] "true" []
      [("post_hi", "hi * 1"), ("post_lo", "lo / 1")] false)
    (json% [[["hi", 9223372036854775807], ["lo", -9223372036854775808],
      ["neg", 2], ["div", -9223372036854775808],
      ["post_hi", 9223372036854775807], ["post_lo", -9223372036854775808]]])
  expect db safe "limit and ordering by output alias"
    (json% {"domains": [["r", "Row"]], "output": [["n", "r.n"]],
      "condition": "true", "order": [["n", "desc"]], "limit": 1})
    (json% [[["n", 2]]])
  for (expr, expected) in [
      ("[2,2] > [2,10]", true), ("[2,2] >= [2,10]", true),
      ("[2,2] < [2,10]", false), ("[2,2] <= [2,10]", false),
      ("[2,2] == [2,10]", false), ("[2,2] != [2,10]", true),
      ("(2,2) > (2,10)", true), ("[9] > [1,2]", true),
      ("([9],0) > ([1,2],0)", true), ("[-2] < [-10]", false),
      ("[0] < []", true), ("[1] > [1,0]", true),
      ("([true,false], 'a b') == ([true,false], 'a b')", true),
      ("['a b'] == ['ab']", false), ("['a  b', 'c'] > ['a b', 'c']", false),
      ("['a\" b'] == ['a\"b']", false), ("['a\\ b'] == ['a\\b']", false),
      ("['é'] > ['z']", true)] do
    expect db safe s!"JSON text comparison in both stages: {expr}"
      (query [("sql", expr)] "true" [] [("post", expr)] false)
      (Lean.toJson [[("sql", expected), ("post", expected)]])
  expect db safe "composite comparison in WHERE"
    (query [("id", "r.id")] "r.items > [2,10]" [("r.id", "asc")])
    (json% [[["id", 2]], [["id", 3]]])
  expect db safe "list field uses text ordering"
    (query [("id", "r.id")] "true" [("r.items", "asc")])
    (json% [[["id", 1]], [["id", 2]], [["id", 3]]])
  expect db safe "list output alias uses text ordering"
    (query [("v", "r.items")] "true" [("v", "desc")])
    (json% [[["v", []]], [["v", [2,2]]], [["v", [2,10]]]])
  expect db safe "tuple sort expression uses text ordering"
    (query [("id", "r.id")] "true" [("(r.items, r.flag)", "asc")])
    (json% [[["id", 1]], [["id", 2]], [["id", 3]]])
  expect db safe "composite sorting precedes limit"
    (json% {"domains": [["r", "Row"]], "output": [["v", "r.items"]],
      "order": [["v", "asc"]], "limit": 1})
    (json% [[["v", [2,10]]]])
  expect db safe "composite SQL NULL survives comparison and sorting"
    (query [("v", "r.pair"), ("equal", "r.pair == r.pair")]
      "r.id == 3" [("r.pair", "asc")] [("post", "v == v")])
    (json% [[["v", null], ["equal", null], ["post", null]]])
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
  expect db safe "bytewise string operators in SQL and postprocessing"
    (query [("lt", "'Z' < 'a'"), ("le", "'Z' <= 'a'"), ("gt", "'a' > 'Z'"),
      ("ge", "'a' >= 'Z'"), ("eq", "'A' == 'a'"), ("ne", "'A' != 'a'"),
      ("unicode", "'é' > 'z'")] "true" []
      [("post", "'Z' < 'a'"), ("post_unicode", "'é' > 'z'")] false)
    (json% [[["lt", true], ["le", true], ["gt", true], ["ge", true],
      ["eq", false], ["ne", true], ["unicode", true], ["post", true],
      ["post_unicode", true]]])
  execute db "UPDATE mathql_backend_test SET label = CASE id WHEN 1 THEN 'a' WHEN 2 THEN 'Z' END"
  expect db safe "string comparison overrides column collation"
    (query [("id", "r.id")] "r.label == 'A'") (json% [])
  expect db safe "string primary-key lookup overrides column collation"
    (query [("n", "TextRow['A'].n")] "true" [] [] false)
    (json% [[["n", null]]])
  expect db safe "ascending string field order and nulls"
    (query [("id", "r.id")] "true" [("r.label", "asc")])
    (json% [[["id", 3]], [["id", 2]], [["id", 1]]])
  expect db safe "descending string output-alias order and nulls"
    (query [("id", "r.id"), ("s", "r.label")] "true" [("s", "desc")])
    (json% [[["id", 1], ["s", "a"]], [["id", 2], ["s", "Z"]],
      [["id", 3], ["s", null]]])
  expect db safe "string sort expression can refer to an output alias"
    (query [("id", "r.id"), ("s", "r.label")] "r.id <= 2"
      [("if s == 'a' then 'Z' else 'a'", "asc")])
    (json% [[["id", 1], ["s", "a"]], [["id", 2], ["s", "Z"]]])
  expect db safe "arithmetic sort expression can refer to an output alias"
    (query [("n", "r.n")] "r.id <= 2" [("n * -1", "asc")])
    (json% [[["n", 2]], [["n", 1]]])
  expect db safe "collated alias sorting precedes limit"
    (json% {"domains": [["r", "Row"]], "output": [["s", "r.label"]],
      "condition": "defined r.label", "order": [["s", "asc"]], "limit": 1})
    (json% [[["s", "Z"]]])

/-- PostgreSQL is opt-in, but a supplied connection must work: errors never become skips. -/
def main : IO Unit := do
  IO.println "SQLite"
  suite (sqliteConnection (← SQLite.«open» ":memory:"))
  match ← IO.getEnv "MATHQL_TEST_POSTGRES" with
  | none => IO.println "SKIP PostgreSQL: set MATHQL_TEST_POSTGRES to a libpq connection string"
  | some conninfo =>
    IO.println "PostgreSQL"
    suite (postgresConnection (← Postgres.«open» conninfo))
