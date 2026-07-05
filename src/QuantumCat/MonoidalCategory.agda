module QuantumCat.MonoidalCategory where

open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.Category using (Category)
open import QuantumCat.Iso using (Iso)
open import Agda.Builtin.Equality using (_≡_)

{-
A Monoidal category consists of:
- a category M
- a functor called tensor product ⊗: M x M -> M, we write
  ⊗(x,y) = x ⊗ y  for objects x,y in M 
  ⊗(f,g) = f ⊗H g for morphisms f,g in M
- an object called the identity object, I ∈ M
- natural isomorphisms:
 - associator a(x,y,z) : ((x ⊗ y) ⊗ z) ≅ (x ⊗ (y ⊗ z))
- left-unitor : l(x) : I ⊗ x ≅ x
- right-unitor : r(x) : x ⊗ I ≅ x
such that following diagrams commute:
- pentagon equation

               a(W,X,Y)⊗id(Z)                 a(W,X⊗Y,Z)
((W⊗X)⊗Y)⊗Z ---------------> (W⊗(X⊗Y))⊗Z ------------> W⊗((X⊗Y)⊗Z) ---
     id(W)⊗a(X,Y,Z)
    ---------------> W⊗(X⊗(Y⊗Z))


               a(W⊗X,Y,Z)                 a(W,X,Y⊗Z)
((W⊗X)⊗Y)⊗Z -----------> (W⊗X)⊗(Y⊗Z) ------------> W⊗(X⊗(Y⊗Z))


- triangle equation

              a(x,I,y)              I(x) ⊗ l(y)
(x ⊗ I) ⊗ y ---------> x (I ⊗ y) -------------> x ⊗ y

              r(x) ⊗ I(Y)
(x ⊗ I) ⊗ y -------------> x ⊗ y


ncatlab.org/nlab/show/monoidal+category
-}
record MonoidalCategory {u w : Universe} (M : Category u w) : Type (usuc (u umax w)) where
  open Category M
  open Iso
  field

    -- operations
    _⊗O_ : (x : Obj) -> (y : Obj) -> Obj -- tensor product on objects
    _⊗H_ : {A1 A2 B1 B2 : Obj} ->
      (f : Hom A1 B1) ->
      (g : Hom A2 B2) ->
      Hom (A1 ⊗O A2) (B1 ⊗O B2) -- tensor product on morphisms

    I : Obj

    associator : {X Y Z : Obj} ->
      Iso M ((X ⊗O Y) ⊗O Z) (X ⊗O (Y ⊗O Z))
    left-unitor : {X : Obj} ->
      Iso M (I ⊗O X) X
    right-unitor : {X : Obj} ->
      Iso M (X ⊗O I) X

  a : {X Y Z : Obj} -> Hom ((X ⊗O Y) ⊗O Z) (X ⊗O (Y ⊗O Z))
  a = to associator 

  l : {X : Obj} -> Hom (I ⊗O X) X
  l = to left-unitor

  r : {X : Obj} -> Hom (X ⊗O I) X
  r = to right-unitor

  field
    -- laws
    -- tensor product is functorial - preserve identity
    tensor-id : {A B : Obj} ->
      (id{A} ⊗H id{B}) ≡ id{A ⊗O B}
    -- tensor product is functorial - preserve composition
    tensor-compose : {A B C D E F : Obj} ->
      (f : Hom A B) ->
      (g : Hom B C) ->
      (h : Hom D E) ->
      (i : Hom E F) ->
      ((f >>> g) ⊗H (h >>> i))
         ≡
      ((f ⊗H h) >>> (g ⊗H i))

    -- associator naturality
    associator-natural : {A0 A1 B0 B1 C0 C1 : Obj} ->
      (f : Hom A0 A1) (g : Hom B0 B1) (h : Hom C0 C1) ->
      (a {A0} {B0} {C0}) >>> (f ⊗H (g ⊗H h))
        ≡
      ((f ⊗H g) ⊗H h) >>> a {A1} {B1} {C1}

    -- left unitor naturality
    left-unitor-natural : {A B : Obj} (f : Hom A B) ->
      l{A} >>> f
        ≡
      (id{I} ⊗H f) >>> l{B}

    -- right unitor naturality
    right-unitor-natural : {A B : Obj} (f : Hom A B) ->
      r{A} >>> f
        ≡
      (f ⊗H id{I}) >>> r{B}
      
    triangle : {X Y : Obj} ->
      (a{X}{I}{Y} >>> (id{X} ⊗H l{Y}))
        ≡
      (r{X} ⊗H id{Y})
      
    pentagon : {W X Y Z : Obj} ->
      a{W ⊗O X}{Y}{Z} >>> a{W}{X}{Y ⊗O Z}
        ≡
      (a{W}{X}{Y} ⊗H id{Z}) >>> (a {W}{X ⊗O Y}{Z} >>> (id{W} ⊗H  a{X}{Y}{Z}))
