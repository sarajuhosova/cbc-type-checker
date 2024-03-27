module Type where
  
open import Haskell.Law
open import Haskell.Prelude

data Type : Set where
  TyNat : Type                  -- natural numbers
  TyArr : (a b : Type) → Type   -- arrow type (i.e. function)
{-# COMPILE AGDA2HS Type deriving Show #-}

instance
  -- instance for equality of types
  iEqType : Eq Type
  iEqType ._==_ TyNat TyNat = True
  iEqType ._==_ (TyArr av au) (TyArr bv bu) = av == bv && au == bu
  iEqType ._==_ _ _ = False
  {-# COMPILE AGDA2HS iEqType #-}

  {-# TERMINATING #-}
  -- proof that this definition of equality satisfies the equality laws
  iLawfulEqType : IsLawfulEq Type
  iLawfulEqType .isEquality TyNat TyNat                 = refl
  iLawfulEqType .isEquality TyNat (TyArr _ _)           = λ ()
  iLawfulEqType .isEquality (TyArr _ _) TyNat           = λ ()
  iLawfulEqType .isEquality (TyArr av au) (TyArr bv bu)
    with (av == bv && au == bu) in h
  ... | True  = congEq₂ TyArr (&&-leftTrue h) (&&-rightTrue h)
  ... | False = λ where 
                  refl → case (&&-eitherFalse {av == bv} {au == bu} h) of λ where
                    (Left fls) → nequality {x = av} fls refl
                    (Right fls) → nequality {x = au} fls refl
    