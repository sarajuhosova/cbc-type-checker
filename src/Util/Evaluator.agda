module Util.Evaluator where

open import Data.String

-- Evaluation errors are strings.
--
EvalError = String

open import Data.Sum.Base
open import Data.Sum.Effectful.Left EvalError public
open import Effect.Monad

-- An Evaluator results in either a result of type a or an EvalError.
--
Evaluator : Set → Set
Evaluator a = EvalError ⊎ a

evalError : {a : Set} → EvalError → Evaluator a
evalError = inj₁

instance
  -- Evaluator is a monad.
  --
  iRawMonadEvaluator : RawMonad Evaluator
  iRawMonadEvaluator = monad _
