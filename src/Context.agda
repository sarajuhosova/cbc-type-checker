module Context {name : Set} where

open import Data.List
open import Lang {name}
open import Util.Scope

private variable
  α : Scope name

data Context : Scope name → Set where
  CtxEmpty  : Context []
  CtxExtend : Context α → (x : name) → Type → Context (x ∷ α)

_,_∶_ : Context α → (x : name) → Type → Context (x ∷ α)
_,_∶_ = CtxExtend
infix 4 _,_∶_

lookupVar : (Γ : Context α) (x : name) (p : x ∈ α) → Type
lookupVar (CtxExtend ctx _ t) x here = t
lookupVar (CtxExtend ctx _ t) x (there p) = lookupVar ctx x p
