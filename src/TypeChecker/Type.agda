module TypeChecker.Type where
  
data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type
