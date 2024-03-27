module Context {@0 name : Set} where

open import Haskell.Prelude
open import Lang {name}
open import Type
open import Util.Scope

private variable
  @0 α : Scope name

data Context : @0 Scope name → Set where
  CtxEmpty  : Context []
  CtxExtend : Context α → (@0 x : name) → Type → Context (x ∷ α)
{-# COMPILE AGDA2HS Context #-}

_,_∶_ : Context α → (@0 x : name) → Type → Context (x ∷ α)
_,_∶_ = CtxExtend
infix 4 _,_∶_
{-# COMPILE AGDA2HS _,_∶_ inline #-}

lookupVar : (Γ : Context α) (@0 x : name) (p : x ∈ α) → Type
lookupVar (CtxExtend ctx _ t) x Here = t
lookupVar (CtxExtend ctx _ t) x (There p) = lookupVar ctx x p
{-# COMPILE AGDA2HS lookupVar #-}
