# Backend tests

Run builds and tests inside WSL, from the `MathQL` directory:

```sh
lake update
python3 prepare_dependencies.py
lake build
lake exe backendTest
```

Lean v4.35.0-rc2 reports deprecated theorem names in leanpostgres's pinned
`lean-json` v0.3.0. That package treats warnings as errors, so a fresh checkout
needs `prepare_dependencies.py` before the first build. The script changes only
the ignored `.lake/packages/json/lakefile.lean` cache entry, allowing those
warnings; it is idempotent and fails if the pinned package layout changes.

The build checks the parser, typechecker, compiler, and postprocessing assertions
in `Test.lean`. `backendTest` runs integration tests against an in-memory SQLite
database. Without `MATHQL_TEST_POSTGRES`, it explicitly reports PostgreSQL as
skipped.

To exercise both drivers, supply a libpq connection string for an existing
PostgreSQL database:

```sh
MATHQL_TEST_POSTGRES='host=WINDOWS_HOST port=5432 dbname=DATABASE user=USER' \
  lake exe backendTest
```

Use `.pgpass` or `PGPASSWORD` for authentication. In WSL with NAT networking,
the Windows host is normally the gateway shown by `ip route show default`.
No credentials or host address are stored in the tests. A supplied connection
that fails to open makes the test fail; it never silently skips PostgreSQL.

Each connection creates its own temporary table. Fixtures use `TEXT` JSON and
integer booleans on SQLite, and `JSONB` and native booleans on PostgreSQL. The
test role needs permission to create temporary tables. Tests neither change
imported tables nor create persistent schemas.

Both backends must produce the same expected JSON for:

- scalar types, SQL nulls, string escaping, and signed 64-bit values;
- overflow errors for literals, negation, arithmetic intermediates, conditions,
  sorting, composite construction, and postprocessing (including presence tests);
- typed scalar and nested tuple projections, arithmetic, and conditionals;
- signed division and division by zero in SQL and postprocessing;
- nested arrays, boolean lists and tuples, postprocessing projections, JSON nulls,
  and JSON equality;
- list/tuple construction across PostgreSQL's 100-argument boundary, including
  empty values, multiple chunks, nested arrays, booleans, and null elements;
- physical column discovery, including undeclared and mixed-case column names;
- explicit null ordering, output aliases, limits, empty results, and empty outputs;
- bytewise string comparisons and sorting, including Unicode, columns with a
  different declared collation, primary-key lookup, and expressions over aliases;
- missing join targets, object lookups without domain variables, and joins across
  multiple domain variables;
- shared postprocessing and dependent postprocessing fields;
- decoding, preparation/execution, and compilation errors, followed by a
  successful request on the same connection.

One test deliberately has backend-specific expectations: ordered JSON
comparison. SQLite's existing renderer compares canonical JSON **text**, whereas
PostgreSQL compares JSONB **structurally**. Thus `[2,2] > [2,10]` is true on SQLite
and false on PostgreSQL. This difference is recorded rather than hidden by
normalizing test output.

String comparisons, string key lookups, and string sort keys explicitly use
SQLite BINARY / PostgreSQL C collation. These match Lean's code-point ordering
for valid UTF-8 strings regardless of the database's default collation. Sort
expressions expand output aliases when SQL cannot resolve a nested alias.

Integers are signed 64-bit values. Evaluated arithmetic outside that range fails
the query, including in postprocessing; it is never clamped or converted to null.
SQLite arithmetic checks reject its implicit promotion to REAL before subsequent
operations can use it. The SQLite cell reader also refuses non-integer values
for integer columns. PostgreSQL retains its native BIGINT overflow errors.
Division by zero remains null, as before. Backend-specific error wording is not
part of the protocol contract.

`NULL` ordering is explicitly aligned with SQLite: ascending puts nulls first,
descending puts them last. Tests specify ordering wherever row order matters.

# Code layout

`Backend.lean` defines `Connection` and `Cursor`. Driver modules under `Backend/`
adapt native statements, cell readers, and metadata queries to those interfaces.
`Execute.lean` owns the single compile/render/collect/postprocess pipeline and
converts driver exceptions to query errors. `Main.lean` selects a connection and
passes the resulting query runner to the shared JSON protocol loop.

The checked expression AST retains types for lists, tuples, and projections.
`Compile.lean` carries that information into the SQL AST; `SQLExpr.lean` uses it
to preserve JSON booleans and nested values and to cast PostgreSQL projections
back to their declared scalar types.
