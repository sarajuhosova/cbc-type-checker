module Term {name : Set} where

open import Data.List
open import Util.Scope
open import Data.String

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α

data TermExc (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → TermExc α
  TLam  : (x : name) (v : TermExc (x ∷ α)) → TermExc α
  TApp  : (u v : TermExc α) → TermExc α
  TRaise : (e : String) → TermExc α
  TCatch : (e : String) → TermExc α → TermExc α → TermExc α
  TDecl  : (e : String) → TermExc α → TermExc α 
