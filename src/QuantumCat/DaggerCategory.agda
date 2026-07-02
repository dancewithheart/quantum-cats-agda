module QuantumCat.DaggerCategory where

open import Agda.Primitive public renaming
  ( Level to Universe -- HoTT terminology
  ; Set to Type       -- HoTT/FP terminology
  ; lzero to u0
  ; lsuc to usuc      -- next universe
  ; _⊔_ to _umax_     -- max of 2 universes
  )

open import Agda.Builtin.Equality using (_≡_)

variable l u w z : Universe

u1 = usuc u0
  
{-
Dagger category (category with involution) is category with extra  operation called dagger

Dagger category is a category C equipped with and involutive contravariant endofunctor †
- for every morphism f : A ->  B exists f † : B -> A
- that is involution: (f †) † = f
- preserve identity: id † = id
- preserver composition

-}
-- https://ncatlab.org/nlab/show/dagger+category
record DaggerCategory (u w : Universe) : Type (usuc (u umax w)) where
  field
    -- types
    Obj  : Type u         -- objects
    Hom  : (source : Obj)
      -> (target : Obj)
      -> Type w           -- home object


    -- operations
    id    : {A : Obj} -> Hom A A -- identify on object
    _>>>_ : {A B C : Obj} -> Hom A B -> Hom B C -> Hom A C -- composition on morphisms
    _†    : {A B : Obj} -> Hom A B -> Hom B A -- dagger (involution)

    -- TODO laws for category: identity and associativity of composition

    -- laws
    dagger-involutive : {A B : Obj} (f : Hom A B) -> (f †) † ≡ f
    dagger-id         : {A : Obj} -> (id {A}) † ≡ id
    dagger-compose    : {A B C : Obj} (f : Hom A B) (g : Hom B C) -> (f >>> g) † ≡ (g †) >>> (f †)
