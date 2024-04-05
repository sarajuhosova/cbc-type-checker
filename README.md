# Correct-by-Construction Type Checking

This repository contains a small example of a correct-by-construction type checker for the [simply-typed lambda calculus](https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus) implemented in [Agda](https://agda.readthedocs.io/en/latest/index.html).

## Setup

To get the code working, follow these steps:

1. Install Agda by following [the instruction on the website](https://agda.readthedocs.io/en/latest/getting-started/installation.html).
2. Install the `standard-library` using the [installation guide](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md).
3. To test that everything works, compile the `src/Everything.agda` file.

## Overview

The type checker is built up using various components, outlined below.
A small example where the type checker is used can be found in the `Everything` module.

### `Util.Scope`

We define the scope (the available variables) as a list of available names:

```agda
Scope : (name : Set) → Set
Scope name = List name
```

Now, to extends scope `α` with name `x`, we simply have to write `x ∷ α`.

To be able to assert a name's availability within the scope, we also define a proof-relevant "in" predicate:

```agda
data _∈_ {name : Set} (x : name) : Scope name → Set where
    here  : ∀ {ns : Scope name}                         → x ∈ (x ∷ ns)
    there : ∀ {n : name} {ns : Scope name} (_ : x ∈ ns) → x ∈ (n ∷ ns)
```

### `Term` and `TypeChecker.Type`

We construct a well-scoped syntax for the language:

```agda
data Type : Set where
  TyNat : Type
  TyArr : (a b : Type) → Type

data Term (α : Scope name) : Set where
  TVar  : (x : name) → x ∈ α → Term α
  TLam  : (x : name) (v : Term (x ∷ α)) → Term α
  TApp  : (u v : Term α) → Term α
```

In our syntax, the identity function (`λ x → x`) would look like this: `TLam "x" (TVar "x" here)`.
This term would type check against type `TyArr TyNat TyNat`, but also against `TyArr (TyArr TyNat TyNat) (TyArr TyNat TyNat)`.

### `TypeChecker.TypingRules`

Next, we specify the typing rules of the language:

```agda
data _⊢_∶_ (Γ : Context α) : Term α → Type → Set where
  TyTVar
    : (p : x ∈ α)
    ----------------------------------
    → Γ ⊢ TVar x p ∶ lookupVar Γ x p

  TyTLam
    : Γ , x ∶ a ⊢ u ∶ b
    -------------------------------
    → Γ ⊢ TLam x u ∶ TyArr a b

  TyTApp
    : Γ ⊢ u ∶ (TyArr a b)
    → Γ ⊢ v ∶ a
    ------------------------------------
    → Γ ⊢ TApp u v ∶ b

infix 3 _⊢_∶_
```

Now we can write `Γ ⊢ u ∶ t` for `u` has type `t` under context `Γ` (where `u` and `Γ` are parametrised with scope `α`).

### `Util.Context`

We begin the implementation of the type checker by defining a variable context as an `All`.
We parametrise the context on `Scope` and define a variable lookup function:

```agda
Context : (v : Set) → (α : Scope name) → Set
Context v α = All (λ _ → v) α

lookupVar : (Γ : Context v α) (x : name) (p : x ∈ α) → v
lookupVar (v ∷ _  ) x here = v
lookupVar (_ ∷ ctx) x (there p) = lookupVar ctx x p
```

Given a predicate `P`, `All P xs` means that every element in `xs` satisfies `P`.
Here it allows us to assign a type to each variable in the scope.

Note that `Context` takes a parameter `v`, which allows us to determine what kind of value we want to assign to variables.
When used in a type checker, we pass `Type` as an argument for `v`.
If we wanted to use `Context` in an interpreter instead, we would pass the value type.

### `Util.Evaluator`

We define a simple evaluator monad with `String` errors:

```agda
EvalError = String

Evaluator : Set → Set
Evaluator a = EvalError ⊎ a
```

### `TypeChecker`

Type-checking function application requires conversion checking, i.e. checking whether two types are equal.
In simply-typed lambda calculus, conversion is just definitional equality, so implementing a conversion checker is straightforward:

```agda
convert : (a b : Type) → Evaluator (a ≡ b)
convert TyNat TyNat = return refl
convert (TyArr la lb) (TyArr ra rb) = do
  refl ← convert la ra
  refl ← convert lb rb
  return refl
convert _ _ = evalError "unequal types"
```

Finally, we define the [bidirectional-style type checking functions](https://plfa.github.io/Inference/) mutually:

```agda
inferType : ∀ (Γ : Context α) u             → Evaluator (Σ[ t ∈ Type ] Γ ⊢ u ∶ t)
checkType : ∀ (Γ : Context α) u (ty : Type) → Evaluator (Γ ⊢ u ∶ ty)

inferType ctx (TVar x index) = return (lookupVar ctx x index , TyTVar index)
inferType ctx (TLam x body) = evalError "cannot infer the type of a lambda"
inferType ctx (TApp lam arg) = do
  (TyArr a b) , gtu ← inferType ctx lam
    where _ → evalError "application head should have a function type"
  gtv ← checkType ctx arg a
  return (b , TyTApp gtu gtv)

checkType ctx (TLam x body) (TyArr a b) = do
  tr ← checkType (ctx , x ∶ a) body b
  return (TyTLam tr)
checkType ctx (TLam x body) _ = evalError "lambda should have a function type"
checkType ctx term ty = do
  (t , tr) ← inferType ctx term
  refl ← convert t ty
  return tr
```

Things to note:
* Both `inferType` and `checkType` return a typing judgement for the specific input term (and type, in case of `checkType`), so we know not just that we get a correct typing derivation but also that it is a derivation for the given input(s).
* We make use of Agda's `do`-notation for the `Evaluator` monad.
  This includes the ability to pattern match on the output of a statement in a `do`-block, and the use of `where` to deal with the cases that are not on the "happy path" (in this case, by throwing an error if the head of an application does not have a function type).
* In the final case for `checkType`, we call the conversion checker, which (if it succeeds) returns an equality proof.
  We then match this equality proof against `refl`, unifying the left- and right-hand sides of the equality for the remainder of the `do`-block.
* Since we return an error message instead of providing evidence of a contradiction in the negative cases, our type checker is _sound_ but _not complete_, i.e. "if it returns a derivation, we know it is correct; but there is nothing to prevent us from writing a function that always returns an error, even when there exists a correct derivation" (see [PLFA: Inference](https://plfa.github.io/Inference/#soundness-and-completeness)).