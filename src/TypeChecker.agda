module TypeChecker {@0 name : Set} where

open import Haskell.Prelude
open import Haskell.Law
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Extra.Sigma
open import Context {name}
open import Lang {name}
open import TypingRules {name}
-- open import Util.Sigma
open import Util.Scope
open import Util.Evaluator

private variable
  @0 α : Scope name
  u : Term α

convert : (a b : Type) → Evaluator (a ≡ b)
convert TyNat TyNat = return refl
convert (TyArr la lb) (TyArr ra rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert _ _ = evalError "unequal types"

inferType : ∀ (Γ : Context α) u             → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type) → Evaluator (Γ ⊢ u ∶ ty)

inferType ctx (TVar x index) = return (lookupVar ctx x index , TyTVar index)
inferType ctx (TLam x body) = evalError "cannot infer the type of a lambda"
inferType ctx (TApp lam arg) = do
  tLam , gtu ← inferType ctx lam
  case tLam of λ where
    (TyArr a b) {{h}} → do
      gtv ← checkType ctx arg a
      return (b , TyApp (subst0 (λ x → TyTerm ctx lam x) h gtu) gtv)
    _ → evalError "application head should have a function type"

checkType ctx (TLam x body) ty =
  case (inspect ty) of λ where
    (TyArr a b ⟨ refl ⟩) → do
      tr ← checkType (ctx , x ∶ a) body b
      return (TyLam tr)
    _ → evalError "lambda should have a function type"
checkType ctx term ty = do
  (t , tr) ← inferType ctx term
  refl ← convert t ty
  return tr
