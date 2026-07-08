{-# OPTIONS --exact-split --safe #-}

module QuantumCat.Functor where

open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.Category using (Category)
open import Agda.Builtin.Equality using (_≡_; refl)

{-
Given categories C,D a functor F:C->D consis of:
* a function F:Obj(C) -> Obj(D)
* for any pair of objects x,y ∈ Obj(C), a function F:Hom(x,y) -> Hom(F(X),F(Y))
such that:
* F preserves identities: for any object X ∈ C, F(1(x)) = 1(F(x))
* F preserves composition: for any pair of morphisms f:x->y,g:y->z in C,
  F(fg) = F(F)F(g)

https://ncatlab.org/nlab/show/functor
-}
record Functor
    {uC wC uD wD : Universe}
    (C : Category uC wC)
    (D : Category uD wD)
    : Type (usuc (uC umax wC umax uD umax wD)) where
  open Category
  private
    module C = Category C
    module D = Category D

  field
    -- operation
    F[_] : C.Obj -> D.Obj  -- map on objects
    fmap : {X Y : C.Obj}       -- map on morphisms
         -> X C.=> Y           -- morphism in C between X and Y
         -> F[ X ] D.=> F[ Y ] -- morphism in D between FX and FY

    -- laws
    -- preserve identity
    F-identity : {X : C.Obj} -> fmap (C.id {X}) ≡ D.id { F[ X ] }
    -- preserve composition (homomorphism)
    F-compose : {X S T : C.Obj}
                (f : X C.=> S)(g : S C.=> T)
             -> fmap (f C.>>> g) ≡ (fmap f) D.>>> (fmap g)

-- endofunctor
EndoFunctor : {uC wC : Universe}
           -> (Category uC wC)
           -> Type (usuc (uC umax wC))
EndoFunctor C = Functor C C

-- identity functor
IdFunctor : {uC wC : Universe}
           -> (C : Category uC wC)
           -> Functor C C
IdFunctor C = record
  { F[_]       = \A -> A
  ; fmap       = \f -> f 
  ; F-identity = refl 
  ; F-compose  = \ f g -> refl
  } where open Category C
