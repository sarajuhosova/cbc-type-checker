module Exceptions {name : Set} {exception : Set} where

open import Data.List
open import Util.Scope
open import Util.Context
open import Data.Empty

-- We'll use annotated types, with annotations being a set of identifiers
-- marking the names of the kinds of exceptions that a computation might throw
Ann = List exception

{- Types with effect annotations (or, alternatively, where the function arrow is
   now a Kleisli morphism) -}
data Type : Set where
  nat    : Type
  _[_]⇒_ : (a : Type) → (φ : Ann) → (b : Type) → Type

private variable
  α : Scope name

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
  TRaise : (e : exception) → Term α
  TCatch : (e : exception) → Term α → Term α → Term α
  TDecl  : (e : exception) → Term α → Term α 

private variable
  x : name
  a b : Type
  u v : Term α
  φ φ₁ φ₂ : Ann
  Ξ : List exception
  e : exception

data _◂_⊢_∶_∣_ (Ξ : List exception) (Γ : Context Type α) : Term α → Type → Ann → Set where

  TyTVar
    : (p : x ∈ α)
    ----------------------------------------
    → Ξ ◂ Γ ⊢ TVar x p ∶ lookupVar Γ x p ∣ φ

  TyTLam
    : Ξ ◂ (Γ , x ∶ a) ⊢ u ∶ b ∣ φ₁  
    -------------------------------------
    → Ξ ◂ Γ ⊢ TLam x u ∶ a [ φ₁ ]⇒ b ∣ φ₂

  TyTApp
    : Ξ ◂ Γ ⊢ u ∶ a [ φ ]⇒ b ∣ φ
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
    ----------------------------
    → Ξ ◂ Γ ⊢ TApp u v ∶ b ∣ φ

  TyTRaise
    : e ∈ Ξ
    → e ∈ φ
    --------------------------
    → Ξ ◂ Γ ⊢ TRaise e ∶ a ∣ φ 

  TyTCatch
    : e ∈ φ → ⊥
    → Ξ ◂ Γ ⊢ u ∶ a ∣ (e ∷ φ)
    → Ξ ◂ Γ ⊢ v ∶ a ∣ φ
      ----------------------------
    → Ξ ◂ Γ ⊢ TCatch e u v ∶ a ∣ φ

  TyTDecl
    : (e ∷ Ξ) ◂ Γ ⊢ u ∶ a ∣ φ
    ---------------------------
    → Ξ ◂ Γ ⊢ TDecl e u ∶ a ∣ φ 

