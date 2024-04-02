module TypingRules {name : Set} where

open import Context {name}
open import Lang {name}
open import Util.Scope

private variable
  x : name
  α : Scope name
  a b : Type
  u v : Term α

data TyTerm (Γ : Context α) : Term α → Type → Set 
  
infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t -- use \∶ to make the symbol

data TyTerm {α} Γ where

  TyTVar
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyLam
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ TyArr a b

  TyApp
    : Γ ⊢ u ∶ (TyArr a b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ TApp u v ∶ b
