module Util.Evaluator where

open import Data.String

EvalError = String

open import Data.Sum.Base
open import Data.Sum.Effectful.Left EvalError public
open import Effect.Monad

Evaluator : Set → Set
Evaluator a = EvalError ⊎ a

evalError : {a : Set} → EvalError → Evaluator a
evalError = inj₁

instance
  iRawMonadEvaluator : RawMonad Evaluator
  iRawMonadEvaluator = monad _
