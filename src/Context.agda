module Context {@0 name : Set} where

open import Data.List.Base
open import Scope
open import Lang {name}

private variable
  @0 α : Scope name

data Context : @0 Scope name → Set where
  CtxEmpty  : Context []
  CtxExtend : Context α → (@0 x : name) → Type → Context (x ∷ α)

_,_∶_ : Context α → (@0 x : name) → Type → Context (x ∷ α)
_,_∶_ = CtxExtend
infix 4 _,_∶_

lookupVar : (Γ : Context α) (@0 x : name) (p : x ∈ α) → Type
lookupVar (CtxExtend ctx _ t) x here = t
lookupVar (CtxExtend ctx _ t) x (there p) = lookupVar ctx x p
