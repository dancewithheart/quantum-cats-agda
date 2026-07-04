module QuantumCat.Category where

open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import Agda.Builtin.Equality using (_≡_)

record Category (u w : Universe) : Type (usuc (u umax w)) where
  field
    -- types
    Obj : Type u -- objects
    Hom : (source : Obj) -> (target : Obj) -> Type w -- home object (morphism, 1-cell)

    -- operations
    id    : {A : Obj} -> Hom A A -- identify on object A
    _>>>_ : {A B C : Obj} -> Hom A B -> Hom B C -> Hom A C -- composition of morphisms
    
    -- laws
    cat-left-id : ∀ {A B : Obj} (f : Hom A B)
      -> id {A} >>> f ≡ f
    cat-right-id : ∀ {A B : Obj} (f : Hom A B)
      -> f >>> id {B} ≡ f
    cat-associativity : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D)
      -> f >>> (g >>> h) ≡ (f >>> g) >>> h
