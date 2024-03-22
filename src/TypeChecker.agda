module TypeChecker {@0 name : Set} where

open import Haskell.Prelude
open import Context {name}
open import Lang {name}
open import TypingRules {name}
open import Util.Scope
open import Util.Evaluator

convert : (a b : Type) → Evaluator (a ≡ b)
convert TyNat TyNat = return refl
convert (TyArr la lb) (TyArr ra rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert _ _ = evalError "unequal types"

private variable
  @0 α : Scope name
  u : Term α

-- inferType : ∀ (Γ : Context α) u → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type) → Evaluator (Γ ⊢ u ∶ ty)

-- inferType = ?
checkType ctx (TVar x x₁) ty = {!   !}
checkType ctx (TLam x term) ty = {!   !}
checkType ctx (TApp term term₁) ty = {!   !}
