module Util.Scope where

open import Data.List

-- Scope is defined as a list of names.
--
Scope : (name : Set) → Set
Scope name = List name

-- An assertion for "x is a member of the scope".
-- 
data _∈_ {name : Set} (x : name) : Scope name → Set where
    here  : ∀ {ns : Scope name}                          → x ∈ (x ∷ ns)
    there : ∀ {n : name} {ns : Scope name} (_ : x ∈ ns) → x ∈ (n ∷ ns)

sempty : {name : Set} → Scope name
sempty = []
