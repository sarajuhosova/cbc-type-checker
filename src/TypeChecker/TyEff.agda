module TypeChecker.TyEff {name : Set} where

open import Term {name}
open import TypeChecker.Type
open import Util.Context {name}
open import Util.Scope

open import Data.String
open import Data.List
open import Data.Empty

-- We'll use annotated types, with annotations being a set of identifiers
-- marking the names of the kinds of exceptions that a computation might throw
Exception = String
Ann = List Exception
open Annotated (List String) 

private variable
  x : name
  α : Scope name
  a b : AnnType
  u v : TermExc α
  φ φ₁ φ₂ : Ann
  Ξ Ξ₁ Ξ₂ : List String
  e₁ e₂ e : String

-- Some operations on annotations, that we might need 
postulate
  addExc : Ann → Exception → Ann

data _◂_⊢_∶_∣_ (Ξ : List String) (Γ : Context AnnType α) : TermExc α → AnnType → Ann → Set where

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
