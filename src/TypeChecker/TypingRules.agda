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

-- type \|- to type ⊢
data _⊢_∶_ (Γ : Context Type α) : Term α → Type → Set where
  ⊢`
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ ` x # p ∶ lookupVar Γ x p

  ⊢ƛ
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ (ƛ x ⇒ u) ∶ a ⇒ b

  ⊢·
    : Γ ⊢ u ∶ (a ⇒ b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ u · v ∶ b

infix 3 _⊢_∶_
