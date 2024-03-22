module Util.Evaluator where

open import Haskell.Prelude

EvalError = String

Evaluator : Set → Set
Evaluator a = Either EvalError a

evalError : {a : Set} → EvalError → Evaluator a
evalError = Left
