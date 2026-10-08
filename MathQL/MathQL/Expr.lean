import MathQL.Name
import MathQL.Operators
import MathQL.Ty

namespace MathQL


mutual

/-- Expressions denoting a domain -/
inductive Domain where
  /-- An identifier -/
  | ident : Ident → Domain
  /-- Object with the given ID -/
  | obj : DomainName → List Expr → Domain
  /-- A field that refers to a domain -/
  | field : Domain → Label → Domain
deriving Repr, BEq

/-- Expressions -/
inductive Expr where
  /-- Integer literal -/
  | int : Int → Expr
  /-- Boolean literal -/
  | bool : Bool → Expr
  /-- String literal -/
  | str : String → Expr
  /-- Predefined constant -/
  | ident : Ident → Expr
  /-- Object ID -/
  | id : Domain → Expr
  /-- Field projection -/
  | field : Domain → Label → Expr
  /-- function call -/
  | call : Ident → List Expr → Expr
  /-- Unary operation -/
  | unop : UnaryOp → Expr → Expr
  /-- Binary operation -/
  | binop : BinaryOp → Expr → Expr → Expr
  /-- Comparison -/
  | compare : ComparisonOp → Ty → Expr → Expr → Expr
  /-- List, retaining the checked element type for JSON construction. -/
  | list : Ty → List Expr → Expr
  /-- Tuple, retaining the checked component types for JSON construction. -/
  | tuple : List Ty → List Expr → Expr
  /-- Tuple projection, retaining the result type for SQL extraction. -/
  | proj : Ty → Expr → Nat → Expr
  /-- Conditional expression -/
  | ite : Expr → Expr → Expr → Expr
  /-- Defined? -/
  | defined : Expr → Expr
  /-- Undefined? -/
  | undefined : Expr → Expr
deriving Repr, BEq

end
