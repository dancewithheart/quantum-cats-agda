{-# OPTIONS --exact-split --safe #-}
module QuantumCat.Category where

open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import Agda.Builtin.Equality using (_≡_)

{-
A category C consists of:
* a collection Ob(C) of objects
* for any pair of objects x,y, a set hom(x,y) of morphisms from x to y (if f \member hom(x,y) we write f: x->y)
equipped with:
* for any object x, an identity morphism 1(x): x->x
* for any pair of morphisms f:x->y and g:y->z, a morphism fg:x->z called the composite of f and g
such that:
* for any morphism f:x->y, the left and right unit laws hold:
  1(x)f = f = f1(y)
* for any triple of morphisms f:w->x, g:x->y, h:y->z, the associative law holds:
  fg(h)=f(gh)

https://ncatlab.org/nlab/show/category
-}
record Category (u w : Universe) : Type (usuc (u umax w)) where
  infixl 20 _>>>_
  field
    -- types
    Obj : Type u -- type of objects
    Hom : (X : Obj) -> (Y : Obj) -> Type w -- type of morphisms (home object, 1-cell)

    -- operations
    id    : {X : Obj} -> Hom X X -- identify morphism on object X
    _>>>_ : {A B C : Obj} -> Hom A B -> Hom B C -> Hom A C -- composition of morphisms
    
    -- laws
    cat-left-id : ∀ {A B : Obj} (f : Hom A B)
      -> id {A} >>> f ≡ f
    cat-right-id : ∀ {A B : Obj} (f : Hom A B)
      -> f >>> id {B} ≡ f
    cat-associativity : ∀ {A B C D : Obj} (f : Hom A B) (g : Hom B C) (h : Hom C D)
      -> f >>> (g >>> h) ≡ (f >>> g) >>> h

  -- aliases useful when Hom works like a function
  _=>_ = Hom
