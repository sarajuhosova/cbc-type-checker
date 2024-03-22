module Lang {@0 name : Set} where

open import Data.List.Base
open import Scope

private variable
  @0 α : Scope name

data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type

data Term (@0 α : Scope name) : Set where
  TVar  : (@0 x : name) → x ∈ α → Term α
  TLam  : (@0 x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  