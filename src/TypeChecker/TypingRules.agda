module TypeChecker.TypingRules {name : Set} where

open import Term {name}
open import TypeChecker.Type
open import Util.Context {name}
open import Util.Scope

private variable
  x : name
  α : Scope name
  a b : Type
  u v : Term α

data _⊢_∶_ (Γ : Context Type α) : Term α → Type → Set where
  TyTVar
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyTLam
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ TyArr a b

  TyTApp
    : Γ ⊢ u ∶ (TyArr a b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ TApp u v ∶ b

infix 3 _⊢_∶_
