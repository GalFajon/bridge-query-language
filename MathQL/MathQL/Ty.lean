import MathQL.Name
import MathQL.Operators

namespace MathQL

/-- Types of the query language. -/
inductive Ty where
  | int : Ty
  | bool : Ty
  | string : Ty
  | list : Ty → Ty
  | prod : List Ty → Ty
deriving Repr

mutual

def Ty.beq : Ty → Ty → Bool
  | .int, .int => true
  | .bool, .bool => true
  | .string, .string => true
  | .list a, .list b => Ty.beq a b
  | .prod as, .prod bs => Ty.beqList as bs
  | .int, _ | .bool, _ | .string, _ | .list _, _ | .prod _, _ => false

def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | a :: as, b :: bs => Ty.beq a b && Ty.beqList as bs
  | [], _ :: _ | _ :: _, [] => false

end

instance : BEq Ty := ⟨Ty.beq⟩

mutual

theorem Ty.beq_refl : (a : Ty) → Ty.beq a a = true
  | .int => rfl
  | .bool => rfl
  | .string => rfl
  | .list a => Ty.beq_refl a
  | .prod as => Ty.beqList_refl as

theorem Ty.beqList_refl : (as : List Ty) → Ty.beqList as as = true
  | [] => rfl
  | a :: as => by simp [Ty.beqList, Ty.beq_refl a, Ty.beqList_refl as]

end

mutual

theorem Ty.eq_of_beq : (a b : Ty) → Ty.beq a b = true → a = b := by
  intro a b h
  cases a <;> cases b <;> try first | rfl | exact Bool.noConfusion h
  · exact congrArg Ty.list (Ty.eq_of_beq _ _ h)
  · exact congrArg Ty.prod (Ty.eqList_of_beq _ _ h)

theorem Ty.eqList_of_beq : (as bs : List Ty) → Ty.beqList as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
      simp only [Ty.beqList, Bool.and_eq_true] at h
      rw [Ty.eq_of_beq a b h.1, Ty.eqList_of_beq as bs h.2]
  | [], _ :: _, h | _ :: _, [], h => Bool.noConfusion h

end

instance : LawfulBEq Ty where
  rfl {a} := Ty.beq_refl a
  eq_of_beq {a b} h := Ty.eq_of_beq a b h

mutual

/-- Render a type as a short string for the schema, e.g. `int`, `list int`. -/
def Ty.render : Ty → String
  | .int => "int"
  | .bool => "bool"
  | .string => "string"
  | .list t => s!"list {Ty.render t}"
  | .prod ts => "prod [" ++ Ty.renderList ts ++ "]"

def Ty.renderList : List Ty → String
  | [] => ""
  | [t] => Ty.render t
  | t :: ts => Ty.render t ++ ", " ++ Ty.renderList ts

end

instance : ToString Ty := ⟨Ty.render⟩

/-- The product of a list of types, elided to the type itself for a one-entry list. -/
def Ty.prod' : List Ty → Ty
| [t] => t
| ts => .prod ts

def unaryTy : UnaryOp → Ty × Ty
| .not => (.bool, .bool)
| .neg => (.int, .int)

def binaryTy : BinaryOp → Ty × Ty × Ty
  | .and => (.bool, .bool, .bool)
  | .or => (.bool, .bool, .bool)
  | .add => (.int, .int, .int)
  | .sub => (.int, .int, .int)
  | .mul => (.int, .int, .int)
  | .div => (.int, .int, .int)
