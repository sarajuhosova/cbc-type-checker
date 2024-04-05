module TypeChecker.Type where
  
data Type : Set where
  `ℕ : Type
  _⇒_ : (a b : Type) → Type
