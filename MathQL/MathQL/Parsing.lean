import Std.Internal.Parsec
import Std.Internal.Parsec.String
import MathQL.Input

/-! A parser for MathQL concrete syntax, built on `Std.Internal.Parsec`.
UTF-8 operators (`∈ ∧ ∨ ¬ ≠ ≤ ≥`) and ASCII synonyms (`in && || ! != <= >=`)
are both accepted. -/

namespace MathQL.Parsing

open Std.Internal.Parsec Std.Internal.Parsec.String
open MathQL

private def sepBy1 {α} (p : Parser α) (sep : Parser Unit) : Parser (List α) := do
  let x ← p
  let xs ← many (do sep; p)
  return x :: xs.toList

private def sepBy {α} (p : Parser α) (sep : Parser Unit) : Parser (List α) :=
  (sepBy1 p sep) <|> pure []

private partial def chainl1Core {α} (p : Parser α) (op : Parser (α → α → α)) (l : α) : Parser α :=
  (do let f ← op; let r ← p; chainl1Core p op (f l r)) <|> pure l

/-- One or more `p`, combined left-associatively by `op`. -/
private def chainl1 {α} (p : Parser α) (op : Parser (α → α → α)) : Parser α := do
  let l ← p
  chainl1Core p op l

private def isIdentStart (c : Char) : Bool := c.isAlpha
private def isIdentRest (c : Char) : Bool := c.isAlphanum || c == '_'

private def keywords : List String :=
  ["if", "then", "else", "in", "true", "false", "defined", "undefined"]

/-- A literal token, skipping trailing whitespace. -/
private def tok (s : String) : Parser Unit := do skipString s; ws

/-- A raw identifier, keywords included; `ident` applies the keyword check. -/
private def rawIdent : Parser String := do
  let c ← satisfy isIdentStart
  let cs ← manyChars (satisfy isIdentRest)
  return c.toString ++ cs

/-- An identifier outside `keywords`, skipping trailing whitespace. -/
private def ident : Parser String := attempt do
  let s ← rawIdent
  if keywords.contains s then fail s!"unexpected keyword '{s}'"
  ws
  return s

/-- A keyword whose following character lies outside the identifier characters. -/
private def keyword (s : String) : Parser Unit := attempt do
  skipString s
  notFollowedBy (satisfy isIdentRest)
  ws

private def intLit : Parser Int := do
  let n ← digits
  ws
  return (Int.ofNat n)

private def intLitNat : Parser Nat := do
  let n ← digits
  ws
  return n

/-- One character of a string literal: a doubled quote `''` denotes a single
    quote, every character apart from `'` denotes itself. -/
private def stringChar : Parser Char :=
  attempt (skipString "''" *> pure '\'') <|> satisfy (· != '\'')

/-- A string literal: single-quoted, an embedded quote written by doubling,
    as in `'it''s'`. -/
private def stringLit : Parser String := do
  skipChar '\''
  let s ← manyChars stringChar
  skipChar '\''
  ws
  return s

private def compareOp : Parser ComparisonOp :=
  (tok "≤" *> pure .le) <|> (tok "<=" *> pure .le) <|>
  (tok "≥" *> pure .ge) <|> (tok ">=" *> pure .ge) <|>
  (tok "≠" *> pure .ne) <|> (tok "!=" *> pure .ne) <|>
  (tok "==" *> pure .eq) <|> (tok "=" *> pure .eq) <|>
  (tok "<" *> pure .lt) <|> (tok ">" *> pure .gt)

mutual

private partial def expr : Parser Input.Expr :=
  ifExpr <|> orExpr

private partial def ifExpr : Parser Input.Expr := do
  keyword "if"; let c ← expr
  keyword "then"; let t ← expr
  keyword "else"; let e ← expr
  return .ite c t e

private partial def orExpr : Parser Input.Expr :=
  chainl1 andExpr ((tok "∨" <|> tok "||") *> pure (.binop .or))

private partial def andExpr : Parser Input.Expr :=
  chainl1 cmpExpr ((tok "∧" <|> tok "&&") *> pure (.binop .and))

private partial def cmpExpr : Parser Input.Expr := do
  let l ← addExpr
  (do let op ← compareOp; let r ← addExpr; return .compare op l r) <|> pure l

private partial def addExpr : Parser Input.Expr :=
  chainl1 mulExpr
    ((tok "+" *> pure (.binop .add)) <|> (tok "-" *> pure (.binop .sub)))

private partial def mulExpr : Parser Input.Expr :=
  chainl1 unaryExpr
    ((tok "*" *> pure (.binop .mul)) <|> (tok "/" *> pure (.binop .div)))

private partial def unaryExpr : Parser Input.Expr :=
  (do keyword "defined"; let e ← unaryExpr; return .defined e) <|>
  (do keyword "undefined"; let e ← unaryExpr; return .undefined e) <|>
  (do (tok "¬" <|> tok "!"); let e ← unaryExpr; return .unop UnaryOp.not e) <|>
  (do tok "-"; let e ← unaryExpr; return .unop UnaryOp.neg e) <|>
  postfixExpr

private partial def postfixExpr : Parser Input.Expr := do
  let e ← atomExpr
  postfixProj e

/-- Apply postfix projections: `.i` (a numeral) a tuple projection, `.label` a
    field projection. -/
private partial def postfixProj (e : Input.Expr) : Parser Input.Expr :=
  (do let i ← attempt (do tok "."; intLitNat); postfixProj (.proj e i)) <|>
  (do let l ← attempt (do tok "."; ident); postfixProj (.field e l)) <|>
  pure e

private partial def atomExpr : Parser Input.Expr :=
  (do let n ← intLit; return .int n) <|>
  (keyword "true" *> pure (.bool true)) <|>
  (keyword "false" *> pure (.bool false)) <|>
  (do let s ← stringLit; return .str s) <|>
  (do tok "["; let items ← sepBy expr (tok ","); tok "]"; return .list items) <|>
  parenOrTupleExpr <|>
  idExpr <|>
  identObjOrCallExpr

/-- The primary key of an object, `id(e)`; a bare `id` is an ordinary identifier. -/
private partial def idExpr : Parser Input.Expr := do
  attempt (do keyword "id"; tok "(")
  let e ← expr
  tok ")"
  return .id e

/-- A bare identifier `x`, an object `D[e₁, …, eₙ]`, or a call `f(e₁, …, eₙ)`. -/
private partial def identObjOrCallExpr : Parser Input.Expr := do
  let x ← ident
  (do tok "["; let es ← sepBy expr (tok ","); tok "]"; return .obj x es) <|>
  (do tok "("; let es ← sepBy expr (tok ","); tok ")"; return .call x es) <|>
  pure (.ident x)

private partial def parenOrTupleExpr : Parser Input.Expr := do
  tok "("
  let e ← expr
  let es ← many (do tok ","; expr)
  tok ")"
  return match es.toList with
    | [] => e
    | es => .tuple (e :: es)

end

/-- Run a parser over an entire string, requiring it to consume all input. -/
private def runComplete {α} (p : Parser α) (s : String) : Except String α :=
  (do ws; let r ← p; eof; return r).run s

/-- Parse an expression from a string. Used by the JSON query decoder. -/
def parseExpr : String → Except String Input.Expr := runComplete expr

/-- Parse a single identifier from a string. -/
def parseIdent : String → Except String String := runComplete ident

end MathQL.Parsing
