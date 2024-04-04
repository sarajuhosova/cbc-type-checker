module Everything where

open import Agda.Builtin.String

name = String

open import Term {name}
open import TypeChecker {name}
open import TypeChecker.Type
open import TypeChecker.TypingRules {name}
open import Util.Context {name}
open import Util.Evaluator
open import Util.Scope

private
  open import Agda.Builtin.Equality

  open import Effect.Monad
  open RawMonad ⦃ ... ⦄

  id-fun : Term sempty
  id-fun = TLam "x" (TVar "x" here)

  id-type : Type
  id-type = TyArr TyNat TyNat

  id-tc : Evaluator (cempty ⊢ id-fun ∶ id-type)
  id-tc = checkType cempty id-fun id-type

  test-id : id-tc ≡ return (TyTLam (TyTVar here))
  test-id = refl
