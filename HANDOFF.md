# Handoff: MathQL in Lean

This repository and `../bridge-mcp` are developed in tandem. They hold **two
implementations of one language**, MathQL: in Lean here, in Python there. `bridge-mcp` is
what ships as the MCP server. See `../bridge-mcp/HANDOFF.md` for that side.

## How the two repositories relate

This is a decision, made on 2026-10-09.

- The design of MathQL is done in Lean. Its concrete syntax, abstract syntax and
  type-checking are defined in `bridge-query-language`: in `LANGUAGE.md` and in the Lean
  implementation under `MathQL/`. The Python implementation in `bridge-mcp` follows them.
- Incidental functionality may differ between the two implementations. Extra
  database-declared functions are the standing example. The MCP tools of `bridge-mcp`,
  such as `compile`, are not part of the language at all.
- The boundary between design and incidental functionality is not drawn more precisely
  than this. When a change could fall on either side, ask.

Commit `9e7a499` in `bridge-mcp` added the division operator `/` to Python first, which is
the wrong order under this rule. The decision is that Lean catches up; the operator stays
in Python.

## Work to be done

These are decided. Each is to be done, in this repository first.

1. **Add the division operator.** See *The division operator* below.
2. **Fix the encoding of booleans nested in JSON.** See *The boolean encoding bug* below.

## State

On `main` at `197c6d7 versions`, working tree clean, in step with `origin/main`. A branch
`mathql-lean` sits at the same commit. Verified on 2026-10-09:

- `cd MathQL && lake exe test` — exits 0, no failures.
- Toolchain `leanprover/lean4:v4.35.0-rc2`; `MathQL/.lake/build/bin` holds built `mathql`
  and `test` binaries.
- `data/graphs-small.db` is present. `data/sym-ob-small.db` is **not** — it is a ≈ 300 MB
  download from <https://www.andrej.com/tmp/sym-ob-small.db>, so `MathQL/SymObSmallDB.lean`
  is exercised only as far as compilation.

`197c6d7` changed `MathQL/lean-toolchain` and `MathQL/lake-manifest.json` and nothing else.

### Moving to another machine

`MathQL/lakefile.lean` requires leansqlite **over SSH**:

```
require leansqlite from git "git@github.com:leanprover/leansqlite.git" @ "main"
```

pinned in `lake-manifest.json` at `0d36e6d34f6861ed37185646b2e5d7a9eff46281`. A machine
without an SSH key registered with GitHub cannot fetch it and `lake build` fails. The
first build also compiles a bundled SQLite amalgamation, so it needs a C compiler and takes
several minutes.

## The division operator

`bridge-mcp` commit `9e7a499` added the division operator `/` to the Python
implementation: multiplication's precedence, left-associative, `Int × Int → Int`. The
seven sites it takes here, each the exact analogue of a Python one:

| what | file |
| --- | --- |
| the constructor | `MathQL/MathQL/Operators.lean:17`, beside `mul` in `BinaryOp` |
| the parser | `MathQL/MathQL/Parsing.lean:114`, `mulExpr`'s `chainl1` — give it the `<\|>` shape `addExpr` already has for `+` and `-` |
| the typing | `MathQL/MathQL/Ty.lean:103`, `binaryTy`, `(.int, .int, .int)` |
| the SQL text | `MathQL/MathQL/SQLExpr.lean:49`, `renderBinop` |
| the evaluator | `MathQL/MathQL/Execute.lean:69`, `evalBinop`'s `.mul` case |
| the specification | `LANGUAGE.md:63` (the grammar) and `LANGUAGE.md:96` (`⊙ ∈ {+,-,*}`) |
| the grammar document | `docs/query-grammar.md:139`, and its precedence list |

### The trap: Lean's `/` on `Int` is the wrong division

The operator must mean what SQLite's `/` means, because the condition, output and order
clauses reach the database as SQL and only the postprocess entries are evaluated in Lean.
The two must agree. Measured under this toolchain:

| expression | SQLite | Lean `/` (`Int.ediv`) | `Int.tdiv` |
| --- | --- | --- | --- |
| `7 / 2` | 3 | 3 | 3 |
| `-7 / 2` | **-3** | **-4** | -3 |
| `7 / -2` | -3 | -3 | -3 |
| `-7 / -2` | **3** | **4** | 3 |

So **`Int.tdiv` is the one to use, not `/`**. Lean's `/` on `Int` disagrees with SQLite in
two of the four sign combinations. (Python's `//` floors and disagrees in two as well, which
is why `bridge-mcp`'s `execute._quotient` computes the magnitude and reapplies the sign.)

Second trap: `(7 : Int) / 0` evaluates to `0` in Lean, silently, where SQLite yields `NULL`.
`evalBinop` returns a `Result`, so a zero divisor must fail explicitly there; the Python
side raises `MathQLError`, which its postprocess evaluator already turns into the absent
value. Check how an `Execute.lean` failure surfaces in a postprocess column before
choosing the shape.

A test should run each sign combination through both stages — the SQL path and the
postprocess path — on one row and check they agree, as
`../bridge-mcp/tests/test_execute.py` does.

## The boolean encoding bug

The bug was found in the Python implementation. It has not been checked here, but this
implementation builds tuples and lists the same way, with `json_array`, so it probably has
it too. Confirm that first.

Verified on 2026-10-09 through the `bridge-mcp` server:

- A boolean at the top level of a row comes back correctly, as `true` or `false`.
- A boolean inside a tuple or a list comes back as `1` or `0`.
  `(g.is_planar, g.num_vertices)` gives `[1, 3]`; `[g.is_planar, g.is_tree]` gives
  `[1, 0]`.
- The wrong value also reaches the postprocess clause: component 0 of that tuple, projected
  there, is `1`, though its type is `bool`.

The likely cause: tuples and lists are built in SQL with `json_array`, SQLite has no
boolean type and stores `1` and `0`, and the decoder converts a boolean column at the top
level of a row but not a boolean nested inside JSON. The decoder has the type of every
column, so it has what it needs to convert nested values too. This cause is inferred from
the output and has not been traced in the code.

The fix belongs to the realization of the language — how a typed value is stored in SQL and
read back — so it is designed here first, then carried to `bridge-mcp`. A test should
return a boolean at the top level, inside a tuple, inside a list, and through a
postprocess projection, and check that each comes back as `true` or `false`.

## A plan mentioned but not recorded

On 2026-10-09 the user recalled a plan to let MathQL queries refer directly to Python
functions. Neither repository and no saved session transcript records it. Ask the user
what it is before acting on it.

The nearest existing mechanism is the *postprocess function*: a function implemented in
the host language, declared by a database, and callable by name from the `postprocess`
clause alone, since the other clauses run in SQLite. In Python it is `PostFunction` in
`bridge-mcp/src/bridge_mcp/mathql/database.py`; in Lean, `postFunction` in
`MathQL/MathQL/Database.lean`. No real database declares one. The only one is `plus`, in the
test databases of both repositories.

## Facts the next session will meet

- `LANGUAGE.md` is the specification of record. `bridge-mcp` keeps a separate grammar
  document, `src/bridge_mcp/mathql/query-grammar.md`, maintained by hand, so the two can
  drift.
