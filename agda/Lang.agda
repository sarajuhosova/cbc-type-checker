module Lang {@0 name : Set} where

open import Haskell.Extra.Dec
open import Haskell.Prelude
open import Util.Scope

data Term (@0 α : Scope name) : Set where
  TVar  : (@0 x : name) → x ∈ α → Term α
  TLam  : (@0 x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
{-# COMPILE AGDA2HS Term deriving Show #-}
  