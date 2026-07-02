module QuantumCat.DaggerCategory where

open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.Category using (Category)
open import Agda.Builtin.Equality using (_≡_)
  
{-
Dagger category (category with involution) is category with extra  operation called dagger

Dagger category is a category C equipped with and involutive contravariant endofunctor †
- for every morphism f : A ->  B exists f † : B -> A
- that is involution: (f †) † = f
- preserve identity: id † = id
- preserver composition
-}
-- https://ncatlab.org/nlab/show/dagger+category
record DaggerCategory
    {u w : Universe}
    (Base : Category u w) : Type (usuc (u umax w)) where
  open Category Base
  field
    -- operations
    dagger : {A B : Obj} -> Hom A B -> Hom B A -- involution

    -- laws
    dagger-involutive : {A B : Obj} (f : Hom A B) -> dagger (dagger f) ≡ f
    dagger-id         : {A : Obj} -> dagger (id {A}) ≡ id
    dagger-compose    : {A B C : Obj} (f : Hom A B) (g : Hom B C)
      -> dagger (f >>> g) ≡ (dagger g) >>> (dagger f)
   
