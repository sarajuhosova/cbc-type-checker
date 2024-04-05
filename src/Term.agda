module Term {name : Set} where

open import Data.List
open import Util.Scope

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  `_#_ : (x : name) → x ∈ α → Term α
  -- type \Gl- to get ƛ
  -- type \=> to get ⇒
  ƛ_⇒_ : (x : name) (v : Term (x ∷ α)) → Term α
  -- type \cdot to get ·
  _·_   : (u v : Term α) → Term α

infix  5  ƛ_⇒_
infixl 7  _·_
infix  9  `_#_
  