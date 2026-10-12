# The MathQL language

MathQL is a small typed language for querying databases of mathematical objects. A
query names the domains of objects it ranges over, a condition they must satisfy, and
what to return. This document describes the types, the expression language and its
bidirectional typing, the shape of a query, and how a query is realized against a
concrete database. It tracks the Lean implementation under `MathQL/`. The concrete
syntax and operator precedence of expressions are in
[`docs/query-grammar.md`](docs/query-grammar.md).

## Design goals

- **The condition reads as ordinary mathematics.** The expression language uses the
  familiar operators, so `g.is_planar && g.girth > 4` reads directly.
- **The design follows standard programming-language theory** — an intrinsically
  typed term language with a bidirectional typing judgement.
- A query is consumed programmatically (e.g. over the MCP interface), so it is
  submitted as a **JSON object** whose fields are the parts of a set-builder
  comprehension — the domains, the output, the condition — with the expressions
  inside written in the notation below.

## Types

```
τ ::= Int | Bool | String        scalar (base) types
    | List τ                     list (ordered)
    | τ₁ × ⋯ × τₙ                 product (n = 0 is the unit type)
```

A type is a finite tree over scalars, lists, and products. Domains are named — they
are what a variable ranges over — and a database may declare named *constants*; the
types are exactly those of the grammar above.

`Int`, `Bool`, and `String` are the scalar types, stored as ordinary columns. A `String`
is text in UTF-8, while every identifier is ASCII: a letter followed by letters, digits
and `_`. `List τ` and products are realized as JSON arrays (see *Realization*), so they
too may appear in a query.

## Expressions

An expression denotes either a *value* — a scalar, list, or tuple — or an *object*
of some domain. The object-denoting expressions are:

```
o ::= x                                                -- a bound variable
    | o.ℓ                                              -- a domain field
    | D[e₁, …, eₙ]                                      -- the object with the given key
```

A bound variable denotes the object it ranges over; a *domain field* `o.ℓ` follows
a link to an object of another domain; and `D[e₁, …, eₙ]` denotes the object of `D`
whose primary key is `(e₁, …, eₙ)`. An object appears only as the head of a
projection or under `id`.

The value expressions are:

```
e ::= n | 's' | true | false                          -- literals
    | o.ℓ                                              -- an input field of an object
    | id(o)                                            -- an object's primary key
    | c                                                -- a named constant
    | f(e₁, …, eₙ)                                      -- a function the database declares
    | - e | e + e | e - e | e * e | e / e              -- arithmetic (Int)
    | ¬ e | e ∧ e | e ∨ e                              -- logic (Bool)
    | e = e | e ≠ e | e < e | e ≤ e | e > e | e ≥ e    -- comparison
    | if e then e else e                               -- conditional
    | defined e | undefined e                          -- presence tests
    | (e₁, …, eₙ) | e.i                                 -- product and projection
    | [] | [e₁, …, eₙ]                                  -- list
```

String literals are single-quoted, with a literal quote written doubled (`'it''s'`).
ASCII synonyms: `∧`=`&&`, `∨`=`||`, `¬`=`!`, `≤`=`<=`, `≥`=`>=`, `≠`=`!=`, `=`=`==`.

`e₁ / e₂` is the quotient truncated toward zero, so `-7 / 2` is `-3`. A zero divisor
yields an absent value.

## Typing

The judgement is bidirectional: synthesis `Γ ⊢ e ⇒ τ` computes a type, checking
`Γ ⊢ e ⇐ τ` checks against a given one; a companion judgement `Γ ⊢ o ⇒ D` assigns
each object-denoting expression its domain. The context `Γ` records the bound
variables (each with its domain) and the database's constants. The three modes are
implemented in `Typing.lean`, against the declarative rules in `Rules.lean`:

- **literals** — `n ⇒ Int`, `'s' ⇒ String`, `true`/`false ⇒ Bool`.
- **variable** — if `x` is bound to domain `D`, then `x ⇒ D`.
- **domain field** — if `o ⇒ D` and `ℓ` is a domain field of `D` linking to `D'`,
  then `o.ℓ ⇒ D'`.
- **object by key** — `D[e₁, …, eₙ] ⇒ D` when the `eᵢ` check against the types of
  `D`'s primary key.
- **input field** — if `o ⇒ D` and `ℓ` is an input field of `D` with type `τ`, then
  `o.ℓ ⇒ τ`.
- **id** — if `o ⇒ D` and `D`'s primary key has types `τ₁, …, τₙ`, then
  `id(o) ⇒ τ₁ × ⋯ × τₙ`; a single-column key elides the product.
- **constant** — if the database declares `c : τ`, then `c ⇒ τ`.
- **function** — if the database declares `f : τ₁, …, τₙ → τ` for the clause being
  checked, then `f(e₁, …, eₙ) ⇒ τ` with each `eᵢ ⇐ τᵢ`.
- **arithmetic** — `- e ⇒ Int` with `e ⇐ Int`; `e₁ ⊙ e₂ ⇒ Int` for `⊙ ∈ {+,-,*,/}`,
  both `⇐ Int`.
- **logic** — `¬ e ⇒ Bool` with `e ⇐ Bool`; `e₁ ⊙ e₂ ⇒ Bool` for `⊙ ∈ {∧,∨}`, both
  `⇐ Bool`.
- **comparison** — `e₁ ⊙ e₂ ⇒ Bool` when `e₁ ⇒ τ` and `e₂ ⇐ τ`, the same `τ` on both
  sides, for every comparison `⊙` (`= ≠ < ≤ > ≥`).
- **conditional** — `if b then e₁ else e₂ : τ` with `b ⇐ Bool` and both branches at
  `τ`.
- **presence** — `defined e ⇒ Bool` and `undefined e ⇒ Bool` for any `e ⇒ τ`.
- **product** — `(e₁, …, eₙ) ⇒ τ₁ × ⋯ × τₙ`; `e.i ⇒ τᵢ` when `e ⇒ τ₁ × ⋯ × τₙ`.
- **list** — a list literal `[e₁, …, eₙ]` has type `List τ` when every `eᵢ` has type
  `τ`; `[]` checks against any `List τ`.

All six comparisons share one rule: both sides at a single type, result `Bool`. This
holds at every type — scalars, lists, and products — because lists and products are
realized as JSON arrays, and a comparison of them is SQLite's comparison over those
arrays.

## Queries

A query is the top-level form, submitted as JSON:

```
{ "domains":     [[x, D], …],          (required)
  "output":      [[name, e], …],       (required)
  "condition":   e,                    (optional, default true)
  "order":       [[e, dir], …],        (optional; dir is "asc" or "desc")
  "limit":       n,                    (optional)
  "postprocess": [[name, e], …] }      (optional, default empty)
```

- `domains` binds distinct variables `x₁ ∈ D₁, …`; with more than one binding the
  query ranges over the product of the domains (a join).
- `output` is an ordered list of `[name, e]` pairs; each name is a plain identifier,
  distinct from the other names, and names a result column whose value is the value of
  `e`. The list order is the column order of every row. Each output expression refers
  to the bound variables.
- `condition` is an expression of type `Bool` over the bound variables.
- `order` sorts by expressions, each ascending or descending; an order expression
  may refer to the output columns by name.
- `limit` caps the number of rows.
- `postprocess` is an ordered list of `[name, e]` pairs, each appended to every row as
  a further column. Each expression refers to the output columns and to the entries
  preceding it, and each name is distinct from the output column names and from the
  names of the other entries.

The `postprocess` entries are evaluated outside the database by the server.

A query returns a list of rows — one per combination of objects satisfying the
condition, in the requested order, capped by `limit`. Each row is a list of
`[name, value]` pairs: the output columns in the order `output` names them, then the
postprocess columns in the order `postprocess` names them.

## Absence

A possibly-absent invariant keeps its scalar type — `diameter : Int` — and may be
absent for a given object (a `NULL` column). Absence is observed only through
`defined e` and `undefined e`, which compile to SQL `IS NOT NULL` / `IS NULL`. A
comparison against an absent value yields SQL's unknown (three-valued logic), so such
a row is dropped from the result. An object can be absent too — a domain field or a
`D[…]` whose row is absent — and `defined id(o)` / `undefined id(o)` test the row's
presence.

In `postprocess` the same two forms test the decoded value: `defined e` is `true` when
`e` evaluates to a value other than JSON `null`, and `false` when `e` evaluates to
`null` and when evaluating `e` fails.

## Realization

A database connects the language to storage. It maps:

- a **domain** → a table or view, whose primary-key columns identify the objects;
- an **input field** → a column of that table;
- a **domain field** → a foreign key, compiled to a `LEFT JOIN` of the linked
  table, one join shared by equal object expressions;
- a **constant** → a fixed SQL expression;
- a **function** available in the compiled clauses → the SQL function the database
  names for it;
- a query's **condition** → a SQL `WHERE`; its **output** → selected expressions,
  each result cell decoded at its declared type and returned under the name the
  query gave it; its **order** → `ORDER BY`, dropping a key whose compiled form
  takes the same value in every row and omitting the clause when that leaves no
  key; its **limit** → `LIMIT`.

Every table and every output column of the compiled `SELECT` carries an alias the
compiler generates — `c1`, `c2`, … — and a key of the order clause naming an output
column renders as that column's alias. The compiler draws the names from a predicate
the caller supplies, which accepts a name when no table of the database has a column
of that name.

Lists and products are realized as JSON arrays: a list or tuple literal compiles to
`json_array(…)`, a tuple projection to `json_extract(…)`, and a comparison of lists or
tuples is SQLite's comparison over the (canonical) JSON.

## Implementation

MathQL is a standalone Lean package. Expressions are parsed by a parser combinator
(`Parsing.lean`); a whole query is decoded from JSON (`QueryJson.lean`); it is
elaborated by the bidirectional judgement into an intrinsically-typed `Expr`
(`Rules.lean`, `Typing.lean`), so ill-typed queries are rejected; and it is
compiled to a single SQL `SELECT` (`Compile.lean`, `SQL.lean`). The result cells
are decoded at their declared types into JSON (`Execute.lean`). One `Expr` serves
every clause under two interpretations: `compileExpr` gives the SQL image of the
condition, the output and the order, and `evalPostExpr` evaluates a postprocess entry
over the decoded row.
