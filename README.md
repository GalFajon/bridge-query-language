# MathQL

MathQL is a query language for databases of mathematical objects. An agent (or
a human) asks mathematical questions about mathematical objects — graphs,
maniplexes, and more — and MathQL compiles them to SQL against whatever
database holds those objects. The query language is defined in
[`LANGUAGE.md`](LANGUAGE.md); the design and goals are in [`PLAN.md`](PLAN.md);
[`docs/mathql-intro.md`](docs/mathql-intro.md) is a short introduction.

## Repository layout

```
.
├── LANGUAGE.md        the query language: syntax, types, typing
├── PLAN.md            design and implementation plan
├── docs/              a short introduction
├── MathQL/            a Lean package: parser, compiler, runner
├── python/            database generation and the MCP server
├── data/              the databases and their descriptions
└── lean/              earlier Lean experiments with the typed core
```

## Prerequisites

- **elan** (the Lean toolchain manager). Lake fetches the pinned toolchain
  automatically.
- A **C compiler** (clang or gcc) — the SQLite binding compiles a bundled copy
  of SQLite. On macOS, the Xcode Command Line Tools (`xcode-select --install`).
- **leansqlite** — fetched automatically by Lake as a git dependency (over SSH).
- For the MCP server: Python and the `mathql-mcp` package under `python/`, installed
  editable. It depends on **mcp** (with the `cli` extra) and **networkx**.
- For regenerating the small-graphs database (optional): **nauty** (`geng`) and
  Python with **networkx**.

```
python3 -m venv .venv && source .venv/bin/activate
python -m pip install -e python       # the MCP server and its dependencies
```

## Building MathQL

```
cd MathQL
lake update
python3 prepare_dependencies.py
lake build          # builds the `mathql` executable (and the test runners)
```

The first build fetches the Lean toolchain and compiles the SQLite amalgamation
and PostgreSQL binding, so it takes a few minutes; later builds are fast.
`prepare_dependencies.py` applies the Lean v4.35 compatibility setting to
Lake's ignored `lean-json` cache; see [backend testing](MathQL/TESTING.md).

## Databases

The databases live in `data/`, which `.gitignore` covers.

- **`graphs-small.db`** — all graphs on up to 8 vertices, with invariants.
  Generate it from the repository root:

  ```
  python python/generate_graphs.py
  ```

  Schema and details: [`data/graphs-small-description.md`](data/graphs-small-description.md).

- **`sym-ob-small.db`** — regular rank-4 maniplexes (≈ 300 MB). Download from
  <https://www.andrej.com/tmp/sym-ob-small.db> into `data/`. Schema:
  [`data/sym-ob-small-description.md`](data/sym-ob-small-description.md).

## Running queries

The `mathql` executable opens a database and serves requests over stdin/stdout:
one JSON request per line, one JSON response per line. Run it from the `MathQL/`
directory (it resolves `../data/graphs-small.db` by default, or takes a database
path as its argument):

```
cd MathQL
lake exe mathql
```

- `{"describe": true}` returns the schema: each domain with its fields and types,
  the constants, and example queries.
- A query object returns `{"rows": [...]}` or `{"error": "..."}`. For example:

```
{"domains": [["g", "Graph"]], "output": [["g6", "id(g)"], ["edges", "g.num_edges"]], "condition": "g.num_vertices == 5", "order": [["edges", "desc"]], "limit": 3}
```

`output` is an ordered list of `[column name, expression]` pairs, and its order is
the column order of every row; each row comes back as a list of `[name, value]`
pairs. An optional `postprocess` takes the same pair form and adds further columns.
The output, condition, order and postprocess expressions are all expressions of the
query language. ASCII operators (`== != < <= > >=`, `&& || !`, `defined`/`undefined`)
are recommended; the UTF-8 forms (`∧ ∨ ¬ ≤ ≥ ≠`) are also accepted.

## MCP server

The `mathql-mcp` package under `python/` runs an MCP server exposing MathQL to an
agent, backed by one persistent `mathql` subprocess. After `pip install -e python` it
is the `mathql-mcp` command. It offers:

- `query`, `describe`, `grammar` — run a query, read the schema, read the grammar;
- `edge_list`, `neighbors`, `shortest_path` — decode a graph's `graph6` string into
  its structure, via networkx;
- `max_clique`, `max_independent_set`, `connected_components`, `coloring` — witnesses
  for the clique number, independence number, components, and a proper coloring.

Point an MCP client at the `mathql-mcp` command, or run `mcp dev
python/src/mathql_mcp/server.py` for the inspector.

## Tests

```
cd MathQL
lake exe test       # end-to-end checks against data/graphs-small.db
```

## The language

[`LANGUAGE.md`](LANGUAGE.md) gives the full language: its concrete syntax,
types, and a bidirectional typing judgement, and how it corresponds to the Lean
development.
