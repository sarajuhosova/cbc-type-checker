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

  ƛx⇒x : Term Φ
  ƛx⇒x = ƛ "x" ⇒ (` "x" # here)

  ℕ⇒ℕ : Type
  ℕ⇒ℕ = `ℕ ⇒ `ℕ

  ⊢ƛx⇒x:ℕ⇒ℕ : Evaluator (∅ ⊢ ƛx⇒x ∶ ℕ⇒ℕ)
  ⊢ƛx⇒x:ℕ⇒ℕ = checkType ∅ ƛx⇒x ℕ⇒ℕ

  test : ⊢ƛx⇒x:ℕ⇒ℕ ≡ return (⊢ƛ (⊢` here))
  test = refl
