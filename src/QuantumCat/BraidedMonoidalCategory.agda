{-# OPTIONS --exact-split --safe #-}
module QuantumCat.BraidedMonoidalCategory where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; _umax_; usuc)
open import QuantumCat.Category using (Category)
open import QuantumCat.Iso using (Iso)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)

{-
A braided monoidal category consists of:
* a monoidal category M
* a natural isomorphism called the braiding: B(X,Y): X⊗Y -> Y⊗X
such that these two diagrams commute, called hexagon equations:

          a⁻¹(X,Y,Z)             B(X,Y)⊗Z
X⊗(Y⊗Z) -----------> (X⊗Y)⊗Z ----------> (Y⊗X)⊗Z
 |                                            |
 | B(X,Y⊗Z)                                  | a(Y,X,Z)
 |                                            |
 \/        a⁻¹(Y,Z,X)             Y⊗B(X,Z)    \/   
(Y⊗Z)⊗X <----------- Y⊗(Z⊗X) <---------- Y⊗(X⊗Z) 

          a(X,Y,Z)             X⊗B(Y,Z)    
(X⊗Y)⊗Z ---------> X⊗(Y⊗Z) ----------> X⊗(Z⊗Y)
 |                                          |
 | B(X⊗Y,Z)                                | a⁻¹(X,Z,Y)   
 |                                          |
 \/        a(Z,X,Y)            B(X,Z)⊗Y    \/
Z⊗(X⊗Y) <--------- (Z⊗X)⊗Y <---------- (X⊗Z)⊗Y

https://ncatlab.org/nlab/show/braided+monoidal+category
-}
record BraidedMonoidalCategory
    {u w : Universe}
    {C : Category u w}
    (MC : MonoidalCategory C)
    : Type (usuc (u umax w)) where
  open MonoidalCategory MC
  open Category C
  open Iso

  field -- operations
    braiding : {X Y : Obj} -> Iso C (X ⊗O Y) (Y ⊗O X)

  β : {X Y : Obj} -> (X ⊗O Y) => (Y ⊗O X)
  β = to braiding

  field  -- laws
    braiding-natural : {X1 X2 Y1 Y2 : Obj} ->
      (f : X1 => X2) ->
      (g : Y1 => Y2) ->
      β{X1}{Y1} >>> (g ⊗H f)
        ≡
      (f ⊗H g) >>> β{X2}{Y2}
    
    hexagon1 : {X Y Z : Obj} ->
      β{X}{Y ⊗O Z}
        ≡
      a⁻¹{X}{Y}{Z} >>> ( β{X}{Y} ⊗H id{Z} )
        >>> a{Y}{X}{Z}
        >>> ( id{Y} ⊗H β{X}{Z} ) >>> a⁻¹{Y}{Z}{X}
 
    hexagon2 : {X Y Z : Obj} ->
      β{X ⊗O Y}{Z}
        ≡
      a{X}{Y}{Z} >>> ( id{X} ⊗H β{Y}{Z} ) >>> a⁻¹{X}{Z}{Y}
        >>> ( β{X}{Z} ⊗H id{Y} )
        >>> a{Z}{X}{Y}
