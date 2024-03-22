{-# OPTIONS --allow-unsolved-metas #-}

module Scope where

open import Data.List.Base

-- we define the scope as a list of names
--
Scope : (name : Set) → Set
Scope name = List name

-- we create an assertion of "x is a member of the scope"
-- 
data In {name : Set} (x : name) : Scope name → Set where
    here  : ∀ {ns : Scope name}                          → In x (x ∷ ns)
    there : ∀ {n : name} {ns : Scope name} (_ : In x ns) → In x (n ∷ ns)

syntax In x α = x ∈ α
