module STLC {name : Set} where

open import Data.List.Base
open import Scope

private variable
  @0 x : name
  @0 α β γ : Scope name

data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type

data Term (@0 α : Scope name) : Set where
  TVar  : (@0 x : name) → x ∈ α → Term α
  TLam  : (@0 x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α

private variable
  @0 a b c : Type
  @0 u v w : Term α

data Context : @0 Scope name → Set where
  CtxEmpty  : Context []
  CtxExtend : Context α → (@0 x : name) → Type → Context (x ∷ α)

_,_∶_ : Context α → (@0 x : name) → Type → Context (x ∷ α)
_,_∶_ = CtxExtend
infix 4 _,_∶_

private variable
  @0 Γ : Context α

lookupVar : (Γ : Context α) (@0 x : name) (p : x ∈ α) → Type
lookupVar (CtxExtend ctx _ t) x here = t
lookupVar (CtxExtend ctx _ t) x (there p) = lookupVar ctx x p

data TyTerm (@0 Γ : Context α) : @0 Term α → @0 Type → Set 
  
infix 3 TyTerm
syntax TyTerm Γ u t = Γ ⊢ u ∶ t

data TyTerm {α} Γ where

  TyTVar
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyLam
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ TyArr a b

  TyApp
    : Γ ⊢ u ∶ (TyArr a b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ TApp u v ∶ b
