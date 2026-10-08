import MathQL.Ty
import MathQL.Context
import MathQL.Expr

namespace MathQL

mutual

inductive ExprOfTy : Context → Expr → Ty → Prop where

  | ident : ∀ {Γ : Context} {x t},
        Γ.getIdent x = .ok t →
        ExprOfTy Γ (.ident x) t

  | int : ∀ {Γ n},
        ExprOfTy Γ (.int n) .int

  | bool : ∀ {Γ b},
        ExprOfTy Γ (.bool b) .bool

  | str : ∀ {Γ s},
        ExprOfTy Γ (.str s) .string

  | id : ∀ {Γ e d ts t},
       DomainOfTy Γ e d →
       Γ.getIdTys d = .ok ts →
       Ty.prod' ts = t →
       ExprOfTy Γ (.id e) t

  | field : ∀ {Γ e d l t},
        DomainOfTy Γ e d →
        Γ.getInputFieldTy d l = .ok t →
        ExprOfTy Γ (.field e l) t

  | call : ∀ {Γ f es ts t},
        Γ.function.lookup f = .some (ts, t) →
        TupleOfTy Γ es ts →
        ExprOfTy Γ (.call f es) t

  | unop : ∀ {Γ op e t₁ t₂},
        unaryTy op = (t₁, t₂) →
        ExprOfTy Γ e t₁ →
        ExprOfTy Γ (.unop op e) t₂

  | binop : ∀ {Γ op e₁ e₂ t₁ t₂ t₃}, binaryTy op = (t₁, t₂, t₃) →
        ExprOfTy Γ e₁ t₁ →
        ExprOfTy Γ e₂ t₂ →
        ExprOfTy Γ (.binop op e₁ e₂) t₃

  | compare : ∀ {Γ op e₁ e₂ t},
        ExprOfTy Γ e₁ t →
        ExprOfTy Γ e₂ t →
        ExprOfTy Γ (.compare op t e₁ e₂) .bool

  | tuple : ∀ {Γ es ts},
        TupleOfTy Γ es ts →
        ExprOfTy Γ (.tuple ts es) (.prod ts)

  | proj : ∀ {Γ e ts i t},
        ExprOfTy Γ e (.prod ts) →
        ts[i]? = .some t →
        ExprOfTy Γ (.proj t e i) t

  | list : ∀ {Γ es t},
        ListOfTy Γ es t →
        ExprOfTy Γ (.list t es) (.list t)

  | ite : ∀ {Γ c a b t},
        ExprOfTy Γ c .bool →
        ExprOfTy Γ a t →
        ExprOfTy Γ b t →
        ExprOfTy Γ (.ite c a b) t

  | defined : ∀ {Γ e t},
        ExprOfTy Γ e t →
        ExprOfTy Γ (.defined e) .bool

  | undefined : ∀ {Γ e t},
        ExprOfTy Γ e t →
        ExprOfTy Γ (.undefined e) .bool

inductive DomainOfTy : Context → Domain → DomainName → Prop where
  | ident : ∀ {Γ x d},
      Γ.getDomainIdent x = .ok d →
      DomainOfTy Γ (.ident x) d

  | obj : ∀ {Γ d ts es},
      Γ.getIdTys d = .ok ts →
      TupleOfTy Γ es ts →
      DomainOfTy Γ (.obj d es) d

  | field : ∀ {Γ d d' e l},
      DomainOfTy Γ e d →
      Γ.getDomainField d l = .ok d' →
      DomainOfTy Γ (.field e l) d'

inductive TupleOfTy : Context → List Expr → List Ty → Prop where
  | nil : ∀ {Γ}, TupleOfTy Γ [] []
  | cons : ∀ {Γ e t es ts}, ExprOfTy Γ e t → TupleOfTy Γ es ts → TupleOfTy Γ (e :: es) (t :: ts)

inductive ListOfTy : Context → List Expr → Ty → Prop where
  | nil : ∀ {Γ t}, ListOfTy Γ [] t
  | cons : ∀ {Γ e es t}, ExprOfTy Γ e t → ListOfTy Γ es t → ListOfTy Γ (e :: es) t

end
