module Util.Context {name : Set} where

open import Data.List
open import Term {name}
open import Util.Scope

open import Data.List.Relation.Unary.All

private variable
  α : Scope name
  v : Set

Context : (v : Set) → (α : Scope name) → Set
Context v α = All (λ _ → v) α

-- type \emptyset to get ∅
∅ : Context v Φ
∅ = []

_,_∶_ : Context v α → (x : name) → v → Context v (x ∷ α)
_,_∶_ ctx _ v = v ∷ ctx
infix 4 _,_∶_

lookupVar : (Γ : Context v α) (x : name) (p : x ∈ α) → v
lookupVar (v ∷ _  ) x here = v
lookupVar (_ ∷ ctx) x (there p) = lookupVar ctx x p
