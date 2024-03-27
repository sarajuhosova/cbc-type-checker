module Util.Scope where

open import Haskell.Prelude

-- we define the scope as a list of names
--
Scope : (name : Set) → Set
Scope name = List name

-- we create an assertion of "x is a member of the scope"
-- 
-- after erasure, this essetially becomes the DeBruijn indices
data In {@0 name : Set} (@0 x : name) : @0 Scope name → Set where
    Here  : ∀ {@0 ns : Scope name}                             → In x (x ∷ ns)
    There : ∀ {@0 n : name} {@0 ns : Scope name} (_ : In x ns) → In x (n ∷ ns)
{-# COMPILE AGDA2HS In deriving Show #-}

syntax In x α = x ∈ α
