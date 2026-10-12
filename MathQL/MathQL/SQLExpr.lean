import MathQL.Operators
import MathQL.Ty

namespace MathQL.SQL

/-- The database whose SQL syntax is being generated. Pass this explicitly at
each rendering call; it is selected by the executable's backend argument. -/
inductive Dialect where
  | sqlite
  | postgresql
deriving Repr, BEq

/-- SQL scalar/boolean expressions. -/
inductive Expr where
  | col       : (table column : String) → Expr
  | ref       : String → Expr                  -- an output-column alias; ORDER BY only
  | int       : Int → Expr
  | str       : String → Expr
  | bool      : Bool → Expr
  | null      : Expr
  | call      : String → List Expr → Expr
  | unop      : UnaryOp → Expr → Expr
  | binop     : BinaryOp → Expr → Expr → Expr
  | compare   : ComparisonOp → Expr → Expr → Expr
  | isNull    : Expr → Expr
  | isNotNull : Expr → Expr
  | case      : (cond thn els : Expr) → Expr   -- CASE WHEN cond THEN thn ELSE els END
  | json        : Expr → Expr                  -- json(e), the canonical (minified) text
  | jsonArray   : List Expr → Expr             -- json_array(…)
  | jsonValue   : Ty → Expr → Expr             -- preserve the element's JSON type
  | jsonExtract : Ty → Expr → Nat → Expr       -- extract at its checked result type
deriving Repr

def Expr.jsonArray' : List Expr → Expr
| [e] => e
| es => .jsonArray es

mutual

/-- Does the expression take the same value in every row? -/
def Expr.isConstant : Expr → Bool
  | .int _ | .bool _ | .str _ | .null => true
  | .col _ _ | .ref _ | .call _ _ => false
  | .unop _ e | .isNull e | .isNotNull e | .json e
  | .jsonValue _ e | .jsonExtract _ e _ => e.isConstant
  | .binop _ e₁ e₂ | .compare _ e₁ e₂ => e₁.isConstant && e₂.isConstant
  | .case c t e => c.isConstant && t.isConstant && e.isConstant
  | .jsonArray es => allConstant es

def allConstant : List Expr → Bool
  | [] => true
  | e :: es => e.isConstant && allConstant es

end

/-- The SQL text of a binary operator. -/
def renderBinop : BinaryOp → String
  | .and => "AND" | .or => "OR"
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"

/-- The SQL text of a comparison operator. -/
def renderCompareOp : ComparisonOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- The SQL text of a sort direction. -/
def renderDir : Direction → String
  | .asc => "ASC" | .desc => "DESC"

/-- The SQL text of a unary operator. -/
def renderUnop : UnaryOp → String
  | .not => "NOT" | .neg => "-"

/-- Render an identifier, double-quoted, an embedded quote doubled. -/
def renderIdent (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""

/-- SQLite promotes overflowing integer arithmetic to REAL. Reject it before
another operation or a cell decoder can truncate/clamp it. The scalar subquery
keeps the SQL text linear in the expression size; CASE preserves SQL NULL.
SQLite's abs(minInt64) supplies a native integer-overflow error on failure. -/
private def checkedSQLiteInteger (s : String) : String :=
  s!"(SELECT CASE WHEN typeof(_mathql_integer) IN ('integer', 'null') \
     THEN _mathql_integer ELSE abs(-9223372036854775808) END \
     FROM (SELECT {s} AS _mathql_integer))"

mutual

/-- Render an expression for the selected database. String literals use single
quotes, with an embedded quote doubled. -/
def renderExprWith (dialect : Dialect) : Expr → String
  | .col table column => s!"{table}.{renderIdent column}"
  | .ref name         => name
  | .int n            => match dialect with
      | .sqlite => toString n
      | .postgresql => s!"({n})::bigint"
  | .bool b           => match dialect with
      | .sqlite => if b then "1" else "0"
      | .postgresql => if b then "TRUE" else "FALSE"
  | .str s            => match dialect with
      | .sqlite => "'" ++ s.replace "'" "''" ++ "'"
      | .postgresql => "E'" ++ (s.replace "\\" "\\\\").replace "'" "''" ++ "'"
  | .null             => "NULL"
  | .call f es        => s!"{renderIdent f}({renderArgsWith dialect es})"
  | .unop .neg (.int n) => match dialect with
      | .sqlite => checkedSQLiteInteger s!"- ({n})"
      | .postgresql => s!"({-n})::bigint"
  | .unop .neg e      =>
      let s := s!"- ({renderExprWith dialect e})"
      if dialect == .sqlite then checkedSQLiteInteger s else s
  | .unop op e        => s!"{renderUnop op} ({renderExprWith dialect e})"
  | .binop .div e₁ e₂ => match dialect with
      | .sqlite => checkedSQLiteInteger s!"({renderExprWith dialect e₁} / {renderExprWith dialect e₂})"
      | .postgresql =>
        s!"({renderExprWith dialect e₁} / NULLIF({renderExprWith dialect e₂}, 0))"
  | .binop op e₁ e₂   =>
      let s := s!"({renderExprWith dialect e₁} {renderBinop op} {renderExprWith dialect e₂})"
      match dialect, op with
      | .sqlite, .add | .sqlite, .sub | .sqlite, .mul => checkedSQLiteInteger s
      | _, _ => s
  | .compare op e₁ e₂ => s!"({renderExprWith dialect e₁} {renderCompareOp op} {renderExprWith dialect e₂})"
  | .isNull e         => s!"({renderExprWith dialect e} IS NULL)"
  | .isNotNull e      => s!"({renderExprWith dialect e} IS NOT NULL)"
  | .case c t e       => s!"(CASE WHEN {renderExprWith dialect c} THEN {renderExprWith dialect t} ELSE {renderExprWith dialect e} END)"
  | .json e           => match dialect with
      | .sqlite => s!"json({renderExprWith dialect e})"
      | .postgresql => s!"({renderExprWith dialect e})::jsonb"
  | .jsonArray es     => match dialect with
      | .sqlite => s!"json_array({renderArgsWith dialect es})"
      | .postgresql => s!"jsonb_build_array({renderArgsWith dialect es})"
  | .jsonValue t e    =>
      let s := renderExprWith dialect e
      match dialect, t with
      | .sqlite, .bool => s!"json(CASE WHEN {s} IS NULL THEN 'null' WHEN {s} THEN 'true' ELSE 'false' END)"
      | .sqlite, .list _ | .sqlite, .prod _ => s!"json({s})"
      | .postgresql, .list _ | .postgresql, .prod _ => s!"({s})::jsonb"
      | .postgresql, .string => s!"({s})::text"
      | _, _ => s
  | .jsonExtract t e i => match dialect with
      | .sqlite =>
        let s := s!"json_extract({renderExprWith dialect e}, '$[{i}]')"
        match t with
        | .int => checkedSQLiteInteger s
        | _ => s
      | .postgresql =>
        let s := s!"({renderExprWith dialect e})::jsonb"
        match t with
        | .int => s!"(({s} ->> {i})::bigint)"
        | .bool => s!"(({s} ->> {i})::boolean)"
        | .string => s!"({s} ->> {i})"
        | .list _ | .prod _ => s!"NULLIF({s} -> {i}, 'null'::jsonb)"

/-- Render a comma-separated argument list. -/
def renderArgsWith (dialect : Dialect) : List Expr → String
  | [] => ""
  | [e] => renderExprWith dialect e
  | e :: es => renderExprWith dialect e ++ ", " ++ renderArgsWith dialect es

end

/-- Preserve SQLite rendering for existing callers. -/
def renderExpr : Expr → String := renderExprWith .sqlite

def renderArgs : List Expr → String := renderArgsWith .sqlite
