import MathQL.Context
import MathQL.Expr
import MathQL.Rules

namespace MathQL

structure Query where
  /-- domain variables -/
  vars : List (Ident × DomainName)
  /-- boolean condition -/
  condition : Expr
  /-- output fields, each an alias, the field's type, and the expression -/
  output : List (Ident × Ty × Expr)
  postprocess : List (Ident × Ty × Expr)
  limit : Option Nat
  /-- Retain each key's type so SQL rendering can choose its collation. -/
  order : List (Ty × Expr × Direction)

end MathQL
