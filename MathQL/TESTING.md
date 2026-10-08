# Backend tests

Run builds and tests inside WSL, from the `MathQL` directory:

```sh
lake build
lake exe backendTest
```

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
- typed scalar and nested tuple projections, arithmetic, and conditionals;
- nested arrays, boolean lists, JSON nulls, and JSON equality;
- physical column discovery, including undeclared and mixed-case column names;
- explicit null ordering, output aliases, limits, empty results, and empty outputs;
- missing join targets, object lookups without domain variables, and joins across
  multiple domain variables;
- shared postprocessing and dependent postprocessing fields;
- decoding, preparation/execution, and compilation errors, followed by a
  successful request on the same connection.

One test deliberately has backend-specific expectations: ordered JSON
comparison. SQLite's existing renderer compares canonical JSON **text**, whereas
PostgreSQL compares JSONB **structurally**. Thus `[2,2] > [2,10]` is true on SQLite
and false on PostgreSQL. This difference is recorded rather than hidden by
normalizing test output. String collation and arithmetic outside the supported
signed 64-bit range are still governed by the database.

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
