module TypeChecker {name : Set} where

open import Agda.Builtin.Equality
open import Context {name}
open import Lang {name}
open import TypingRules {name}
open import Util.Scope
open import Util.Evaluator

open import Data.Product

open import Effect.Monad
open RawMonad ⦃ ... ⦄

private variable
  α : Scope name
  u : Term α

-- Type checking function application requires conversion checking,
-- i.e. checking whether two types are equal.
--
convert : (a b : Type) → Evaluator (a ≡ b)
convert TyNat TyNat = return refl
convert (TyArr la lb) (TyArr ra rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert _ _ = evalError "unequal types"

-- Bidirectional style type checking, with two functions defined mutually.
--
-- Both functions return a typing judgement for the specific input term,
-- so we know that we get a correct typing derivation 
-- but also that it is a derivation for the given input(s).
inferType : ∀ (Γ : Context α) u             → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type) → Evaluator (Γ ⊢ u ∶ ty)

inferType ctx (TVar x index) = return (lookupVar ctx x index , TyTVar index)
inferType ctx (TLam x body) = evalError "cannot infer the type of a lambda"
inferType ctx (TApp lam arg) = do
  (TyArr a b) , gtu ← inferType ctx lam
    where _ → evalError "application head should have a function type"
  gtv ← checkType ctx arg a
  return (b , TyTApp gtu gtv)

checkType ctx (TLam x body) (TyArr a b) = do
  tr ← checkType (ctx , x ∶ a) body b
  return (TyTLam tr)
checkType ctx (TLam x body) _ = evalError "lambda should have a function type"
checkType ctx term ty = do
  (t , tr) ← inferType ctx term
  -- we call the conversion checker, which (if it succeeds) returns an equality proof,
  -- unifying the left- and right-hand sides of the equality for the remainder of the do-block
  refl ← convert t ty
  return tr
