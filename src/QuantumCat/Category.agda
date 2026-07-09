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

ACT Course - Lecture 34 - Categories - John Baez
https://math.ucr.edu/home/baez/act_course/lecture_34.html
-}
record Category (u w : Universe) : Type (usuc (u umax w)) where
  infixl 20 _>>>_
  field
    -- types
    Obj : Type u -- type of objects
    _=>_ : (X : Obj) -> (Y : Obj) -> Type w -- type of morphisms (home type, 1-cell)

    -- operations
    id    : {X : Obj} -> X => X -- identify morphism on object X
    _>>>_ : {A B C : Obj} -> A => B -> B => C -> A => C -- composition of morphisms
    
    -- laws
    cat-left-id : ∀ {A B : Obj} (f : A => B)
      -> id {A} >>> f ≡ f
    cat-right-id : ∀ {A B : Obj} (f : A => B)
      -> f >>> id {B} ≡ f
    cat-assoc : ∀ {A B C D : Obj} (f : A => B) (g : B => C) (h : C => D)
      -> f >>> (g >>> h) ≡ (f >>> g) >>> h

  -- aliases useful when Hom works like a function
  Hom = _=>_
