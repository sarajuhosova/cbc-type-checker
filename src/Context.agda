module Context {name : Set} where

open import Data.List
open import Lang {name}
open import Util.Scope

open import Data.List.Relation.Unary.All

private variable
  α : Scope name

Context : (α : Scope name) → Set
Context α = All (λ _ → Type) α

cempty : Context sempty
cempty = []

_,_∶_ : Context α → (x : name) → Type → Context (x ∷ α)
_,_∶_ ctx _ t = t ∷ ctx
infix 4 _,_∶_

lookupVar : (Γ : Context α) (x : name) (p : x ∈ α) → Type
lookupVar (t ∷ _  ) x here = t
lookupVar (_ ∷ ctx) x (there p) = lookupVar ctx x p
