module TypeChecker.Type where
  
data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type

{- Types with effect annotations (or, alternatively, where the function arrow is
   now a Kleisli morphism -}
module Annotated (Ann : Set) where

  data AnnType : Set where
    nat    : AnnType
    _[_]⇒_ : (a : AnnType) → (φ : Ann) → (b : AnnType) → AnnType 
