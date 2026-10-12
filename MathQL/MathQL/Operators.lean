/-! Operators of the query language, shared by the input and the typed syntax. -/

namespace MathQL

/-- Unary operators. -/
inductive UnaryOp where
  | not
  | neg
deriving Repr, Inhabited, BEq

/-- Binary operators. -/
inductive BinaryOp where
  | and
  | or
  | add
  | sub
  | mul
  | div
deriving Repr, Inhabited, BEq

/-- Comparisons. -/
inductive ComparisonOp where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
deriving Repr, Inhabited, BEq

/-- Sort direction for `ORDER BY`. -/
inductive Direction where
  | asc
  | desc
deriving Repr, Inhabited, BEq
