module Util.Evaluator where

open import Haskell.Prelude

-- an evaluation error is simply a string
EvalError = String
{-# COMPILE AGDA2HS EvalError #-}

-- the monad for evaluating the type or expression
Evaluator : Set → Set
Evaluator a = Either EvalError a
{-# COMPILE AGDA2HS Evaluator #-}

-- a smart constructor for an evaluation error
evalError : {a : Set} → EvalError → Evaluator a
evalError = Left
{-# COMPILE AGDA2HS evalError #-}
