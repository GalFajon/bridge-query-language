import MathQL

open MathQL

/-- `plus : (int, int) → int`. -/
def plus : List Lean.Json → Result Lean.Json
  | [a, b] => do
    let m ← a.getInt?
    let n ← b.getInt?
    return .num (m + n)
  | _ => throw "plus expects two arguments"

/-- A toy database for exercising the parser, type-checker, and compiler: one
domain `Graph` with a string primary key and three fields, one SQL function registered
under a SQL name of its own, and one postprocessing function. -/
def toyDB : Database where
  overview := "toy"
  const := []
  domain :=
    [(.domain "Graph",
      { table := "graph"
        column :=
          [(.label "graph6", { column := "graph6", ty := .string, isPrimary := true, doc := "" }),
           (.label "n", { column := "n", ty := .int, isPrimary := false, doc := "" }),
           (.label "planar", { column := "planar", ty := .bool, isPrimary := false, doc := "" }),
           (.label "ds", { column := "ds", ty := .list .int, isPrimary := false, doc := "" })]
        foreignKey := []
        doc := "" })]
  sqlFunction := [(.ident "size", ([.string], .int), { sqlite := "length" })]
  postFunction := [(.ident "plus", ([.int, .int], .int), plus)]
  examples := []

/-- String pairs as a JSON array of two-element arrays. -/
def entries (es : List (String × String)) : Lean.Json :=
  .arr (es.map fun (a, b) => Lean.Json.arr #[Lean.Json.str a, Lean.Json.str b]).toArray

/-- A query in JSON form binding `g` and `h` to `Graph`, with the given output
    (alias, expression) pairs and condition. -/
def jq (output : List (String × String)) (condition : String) : Lean.Json :=
  json% {
    "domains":   [["g", "Graph"], ["h", "Graph"]],
    "output":    $(entries output),
    "condition": $(Lean.toJson condition)
  }

/-- A query in JSON form like `jq`, with an ORDER BY clause. -/
def jqOrder (output : List (String × String)) (condition : String)
    (order : List (String × String)) : Lean.Json :=
  json% {
    "domains":   [["g", "Graph"], ["h", "Graph"]],
    "output":    $(entries output),
    "condition": $(Lean.toJson condition),
    "order":     $(entries order)
  }

/-- A query in JSON form like `jq`, with a `postprocess` stage. -/
def jqPost (output : List (String × String)) (condition : String)
    (post : List (String × String)) : Lean.Json :=
  json% {
    "domains":     [["g", "Graph"], ["h", "Graph"]],
    "output":      $(entries output),
    "condition":   $(Lean.toJson condition),
    "postprocess": $(entries post)
  }

/-- Does the JSON query `j` decode and type-check against `toyDB`? -/
def elaborates (j : Lean.Json) : Bool :=
  (Input.Query.fromJson j |>.bind (checkQuery toyDB) |>.toOption).isSome

/-- A name is a safe alias for `toyDB` when it is none of the column names of `graph`. -/
def toySafeAlias (s : String) : Bool :=
  !["graph6", "n", "planar", "ds", "rowid", "oid", "_rowid_"].contains s.toLower

/-- The SQL text of the JSON query `j` against `toyDB`, or the error. -/
def renderOf (j : Lean.Json) : Except String String :=
  Input.Query.fromJson j |>.bind (checkQuery toyDB)
    |>.bind (compileQuery toyDB toySafeAlias) |>.map toString

/-- Does the JSON query `j` decode, type-check, and compile against `toyDB`? -/
def compiles (j : Lean.Json) : Bool :=
  (renderOf j).toOption.isSome

/-- The result of comparing `a` and `b` at type `t`, or `none` if it failed. -/
def comparison (op : ComparisonOp) (t : Ty) (a b : Lean.Json) : Option Lean.Json :=
  (evalComparison op t a b).toOption

/-- The postprocess fields of the JSON query `j`, evaluated over the output row
    `row`, or `none` when type-checking reports an error. -/
def postOf (j : Lean.Json) (row : List (String × Lean.Json)) :
    Option (List (String × Lean.Json)) :=
  (Input.Query.fromJson j |>.bind (checkQuery toyDB) |>.toOption).bind fun q =>
    (evalPostprocess
      { ident := row.map fun (r : String × Lean.Json) => (.ident r.1, r.2)
        function := toyDB.postFunction.map fun (f, _, impl) => (f, impl) }
      q.postprocess).toOption.map fun ps => ps.map fun (p : Ident × Lean.Json) => (p.1.name, p.2)

-- Well-typed queries.
#guard elaborates (jq [("n", "g.n")] "g.planar")
#guard elaborates (jq [("n", "g.n")] "g.n > 3")
#guard elaborates (jq [("a", "g.n"), ("b", "h.n")] "g.n = h.n")
#guard elaborates (jq [("gid", "id(g)")] "id(g) == 'abc'")
#guard elaborates (jq [("n", "g.n")] "defined g.n")
#guard elaborates (jq [("m", "Graph['abc'].n")] "Graph['abc'].n > 3")

-- The output column names are distinct, and each may carry the name of a variable.
#guard elaborates (jq [("g", "g.n"), ("h", "h.n")] "true")
#guard !elaborates (jq [("n", "g.n"), ("n", "h.n")] "true")

-- The domain variables are distinct.
#guard elaborates (json% { "domains": [["g", "Graph"], ["h", "Graph"]],
                           "output": $(entries [("n", "g.n")]) })
#guard !elaborates (json% { "domains": [["g", "Graph"], ["g", "Graph"]],
                            "output": $(entries [("n", "g.n")]) })

-- The rendering of an empty clause.
#guard match renderOf (json% { "domains": [], "output": $(entries [("x", "2 + 2")]) }) with
  | .ok s => s == s!"SELECT {SQL.renderExpr (.binop .add (.int 2) (.int 2))} AS c1 WHERE 1"
  | .error _ => false
#guard match renderOf (json% { "domains": [],
                               "output": $(entries [("n", "Graph['abc'].n")]) }) with
  | .ok s => s == "SELECT c2.\"n\" AS c1 FROM (SELECT 1)"
                  ++ " LEFT JOIN \"graph\" AS c2 ON c2.\"graph6\" = ('abc' COLLATE \"BINARY\") WHERE 1"
  | .error _ => false
#guard match renderOf (json% { "domains": [["g", "Graph"]], "output": [],
                               "condition": "g.n > 3" }) with
  | .ok s => s == "SELECT 1 FROM \"graph\" AS c1 WHERE (c1.\"n\" > 3)"
  | .error _ => false
#guard match renderOf (json% { "domains": [], "output": [] }) with
  | .ok s => s == "SELECT 1 WHERE 1"
  | .error _ => false

-- Ill-typed queries.
#guard !elaborates (jq [("n", "g.n")] "g.n")            -- a condition is checked at Bool
#guard !elaborates (jq [("b", "g.bogus")] "g.planar")   -- unknown field
#guard !elaborates (jq [("n", "g.n")] "g.planar + 1")   -- Bool used in arithmetic
#guard !elaborates (jq [("n", "g.n")] "id(g) == 3")     -- `id` yields String, the literal Int
#guard !elaborates (jq [("m", "g.n"), ("k", "m + 1")] "true")  -- one output referring to another

-- Ordering by an output alias, bare and inside an expression.
#guard compiles (jqOrder [("m", "g.n * g.n")] "g.planar" [("m", "desc")])
#guard compiles (jqOrder [("m", "g.n")] "true" [("m + 1", "asc")])

-- `id` is an ordinary identifier: an output column named `id` is orderable.
#guard compiles (jqOrder [("id", "g.n")] "true" [("id", "desc")])

-- An output column carrying the name of a real column is not captured: the SQL
-- names the generated alias, and `graph6` appears in it nowhere.
#guard match renderOf (jqOrder [("graph6", "g.n")] "true" [("graph6 * 1", "asc")]) with
  | .ok s => (s.splitOn "graph6").length == 1
  | .error _ => false

-- An order key whose compiled form is the same in every row discriminates nothing,
-- so it is dropped; an integer would otherwise read as a column position, and
-- `- 1` as the position -1, which fails to prepare.
#guard match renderOf (jqOrder [("m", "g.n")] "true" [("1", "asc")]) with
  | .ok s => (s.splitOn "ORDER BY").length == 1
  | .error _ => false
#guard match renderOf (jqOrder [("m", "g.n")] "true" [("1", "asc"), ("g.n", "desc")]) with
  | .ok s => s.endsWith "ORDER BY c1.\"n\" DESC"
  | .error _ => false
#guard match renderOf (jqOrder [("m", "g.n")] "true"
                        [("1", "asc"), ("'abc'", "desc"), ("true", "asc")]) with
  | .ok s => s.endsWith "WHERE 1"
  | .error _ => false
#guard match renderOf (jqOrder [("m", "g.n")] "true"
                        [("-1", "asc"), ("!true", "desc"), ("1 + 0", "asc")]) with
  | .ok s => s.endsWith "WHERE 1"
  | .error _ => false

-- An order key that calls a database function is kept.
#guard match renderOf (jqOrder [("m", "g.n")] "true" [("size('ab')", "asc")]) with
  | .ok s => s.endsWith "ORDER BY \"length\"('ab') ASC"
  | .error _ => false

-- Named SQL functions require an explicit PostgreSQL mapping.
#guard match Input.Query.fromJson (jq [("n", "size('ab')")] "true")
    |>.bind (checkQuery toyDB)
    |>.bind (compileQueryWith .postgresql toyDB toySafeAlias) with
  | .error e => e == "function size is not available on PostgreSQL"
  | .ok _ => false

-- A PostgreSQL mapping changes the emitted function name without changing SQLite.
#guard match Input.Query.fromJson (jq [("n", "size('ab')")] "true")
    |>.bind (checkQuery toyDB)
    |>.bind (compileQueryWith .postgresql
      { toyDB with sqlFunction :=
        [(.ident "size", ([.string], .int),
          { sqlite := "length", postgresql := some "char_length" })] } toySafeAlias) with
  | .ok q => ((SQL.renderQueryWith .postgresql q).splitOn "\"char_length\"").length > 1
  | .error _ => false

-- The alias renders bare in ORDER BY.
#guard match renderOf (jqOrder [("m", "g.n")] "true" [("m", "desc")]) with
  | .ok s => s.endsWith "ORDER BY c3 DESC"
  | .error _ => false

-- Identifiers are quoted; list comparisons canonicalize both sides through json().
#guard match renderOf (jq [("n", "g.n")] "g.ds == [2, 2]") with
  | .ok s => s.endsWith "WHERE ((json(c1.\"ds\") COLLATE \"BINARY\") = (json(json_array(2, 2)) COLLATE \"BINARY\"))"
  | .error _ => false

-- Function calls.

-- A call compiles to the SQL name registered for it.
#guard match renderOf (jq [("n", "g.n")] "size(g.graph6) > 2") with
  | .ok s => s.endsWith "WHERE (\"length\"(c1.\"graph6\") > 2)"
  | .error _ => false

-- A call is an ordinary expression: it nests, and it may be an output column.
#guard compiles (jq [("k", "size(g.graph6)")] "size(g.graph6) > size('ab')")

-- The two function tables are disjoint, so each name is callable on one side
-- only: `size` compiles to SQL, `plus` runs during postprocessing.
#guard !elaborates (jq [("n", "g.n")] "plus(g.n, 1) > 3")
#guard !elaborates (jqPost [("s", "id(g)")] "true" [("k", "size(s)")])

-- Argument types and arity are checked at a call.
#guard !elaborates (jq [("n", "g.n")] "size(g.n) > 2")

-- `foo(3)` parses; the checker looks `foo` up in the SQL function table.
#guard !elaborates (jq [("n", "foo(3)")] "true")

-- Postprocessing.

-- Well-formed stages: an int literal, a bare output reference, a call.
#guard elaborates (jqPost [("n", "g.n")] "true" [("k", "3")])
#guard elaborates (jqPost [("n", "g.n")] "true" [("k", "n")])
#guard elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)")])
#guard elaborates (jqPost [("n", "g.n")] "true" [])

-- Sequential (let-chain) scoping: an entry may use any *earlier* entry.
#guard elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)"), ("m", "plus(k, 2)")])

-- The checker rejects a forward reference.
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(m, 1)"), ("m", "n")])

-- Shadowing, both cases. `Γ.ident` is seeded with the output fields and grows by
-- one per entry, so a single lookup before binding rejects each of these.
#guard !elaborates (jqPost [("n", "g.n")] "true" [("n", "3")])            -- shadows an output
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "3"), ("k", "4")]) -- rebinds an earlier entry

-- Arity.
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(1)")])
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(1, 2, 3)")])

-- Argument type: `id(g)` is a String, `plus` wants Ints.
#guard !elaborates (jqPost [("s", "id(g)")] "true" [("k", "plus(s, 1)")])

-- Unknown function, and unknown identifier.
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "bogus(1, 2)")])
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "plus(zzz, 1)")])

-- Postprocessing sees the query's output columns; its context holds those columns
-- alone, so `g.n` is an error here.
#guard !elaborates (jqPost [("n", "g.n")] "true" [("k", "g.n")])

-- Both clauses are arrays: the decoder requires an array and reports an object.
#guard !elaborates (json% {
  "domains":     [["g", "Graph"]],
  "output":      [["n", "g.n"]],
  "condition":   "true",
  "postprocess": {"k": "plus(n, 1)"}
})
#guard !elaborates (json% {
  "domains":   [["g", "Graph"]],
  "output":    {"n": "g.n"},
  "condition": "true"
})

-- Output columns keep the order they were written in; `Lean.Json` returns an
-- object's keys sorted.
#guard match renderOf (jq [("zeta", "g.n"), ("alpha", "g.n")] "true") with
  | .ok s => s.startsWith "SELECT c1.\"n\" AS c3, c1.\"n\" AS c4"
  | .error _ => false

-- Postprocess fields are computed after SQL: the rendered SQL names neither the
-- field `k` nor the function `plus`.
#guard match renderOf (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)")]) with
  | .ok s => (s.splitOn "k").length == 1 && (s.splitOn "plus").length == 1
  | .error _ => false

-- Postprocessing evaluation, over a row supplied directly.

-- A call runs during postprocessing, on the output row.
#guard postOf (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)")]) [("n", json% 5)]
       == some [("k", json% 6)]

-- Each entry sees the values of the earlier ones.
#guard postOf (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)"), ("m", "k * 2")])
         [("n", json% 5)]
       == some [("k", json% 6), ("m", json% 12)]

-- An entry whose evaluation fails becomes null, and null propagates.
#guard postOf (jqPost [("n", "g.n")] "true" [("k", "plus(n, 1)"), ("m", "k * 2")])
         [("n", json% "not a number")]
       == some [("k", Lean.Json.null), ("m", Lean.Json.null)]

-- Division truncates toward zero, as SQLite's `/` does.
#guard ([(7, 2, 3), (-7, 2, -3), (7, -2, -3), (-7, -2, 3), (1, 2, 0), (0, 5, 0)]
          : List (Int × Int × Int)).all fun (a, b, q) =>
  postOf (jqPost [("a", "g.n"), ("b", "h.n")] "true" [("q", "a / b")])
    [("a", .num a), ("b", .num b)]
  == some [("q", .num q)]

-- A zero divisor makes the entry null, as SQLite's `/` does.
#guard postOf (jqPost [("a", "g.n")] "true" [("q", "a / 0"), ("u", "undefined (a / 0)")])
         [("a", json% 7)]
       == some [("q", Lean.Json.null), ("u", json% true)]

-- `*` and `/` share a precedence level and associate to the left.
#guard postOf (jqPost [("a", "g.n")] "true" [("p", "a * 6 / 4"), ("q", "a * 12 / 2 / 3")])
         [("a", json% 2)]
       == some [("p", json% 3), ("q", json% 4)]

-- Comparison is evaluated at the type the term carries, matching what the same
-- expression compiles to in SQL: numeric at int and bool, by code point at
-- string, and by canonical JSON text at list and prod.
#guard comparison .lt .int (.num 2) (.num 10) == some (json% true)
#guard comparison .lt .bool (.bool false) (.bool true) == some (json% true)
#guard comparison .lt .string (.str "Z") (.str "a") == some (json% true)
#guard comparison .gt (.list .int) (json% [2, 2]) (json% [2, 10]) == some (json% true)
#guard comparison .eq (.prod [.int, .string]) (json% [1, "a"]) (json% [1, "a"]) == some (json% true)
#guard comparison .ne (.prod [.int, .string]) (json% [1, "a"]) (json% [1, "b"]) == some (json% true)

-- A null operand makes the comparison null.
#guard comparison .lt .int Lean.Json.null (.num 5) == some Lean.Json.null
#guard comparison .eq .string (.str "a") Lean.Json.null == some Lean.Json.null

-- A comparison at a list type, through the whole postprocess path.
#guard postOf (jqPost [("d", "g.ds")] "true" [("b", "d == [2, 2]")]) [("d", json% [2, 2])]
       == some [("b", json% true)]

-- `defined` and `undefined` identify a raise with null: a present value is defined,
-- and both a null value and a failed evaluation are undefined.
#guard postOf (jqPost [("n", "g.n")] "true" [("a", "defined n"), ("b", "undefined n")])
         [("n", json% 5)]
       == some [("a", json% true), ("b", json% false)]
#guard postOf (jqPost [("n", "g.n")] "true" [("a", "defined n"), ("b", "undefined n")])
         [("n", Lean.Json.null)]
       == some [("a", json% false), ("b", json% true)]
#guard postOf (jqPost [("n", "g.n")] "true"
         [("a", "defined plus(n, 1)"), ("b", "undefined plus(n, 1)")])
         [("n", json% "not a number")]
       == some [("a", json% false), ("b", json% true)]

-- A null output column is undefined in a postprocess entry, as `IS NULL` finds it
-- in a condition.
#guard postOf (jqPost [("n", "g.n")] "true" [("k", "undefined n")]) [("n", Lean.Json.null)]
       == some [("k", json% true)]

-- SQL expression rendering, printed for review.
#eval IO.println (toString (SQL.Expr.binop .and
  (.compare .gt (.col "g" "num_vertices") (.int 3)) (.col "g" "is_planar")))

def main : IO Unit := pure ()
