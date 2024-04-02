module Lang {name : Set} where

open import Data.List
open import Util.Scope

private variable
  α : Scope name

data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  