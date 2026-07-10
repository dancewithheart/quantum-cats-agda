{-# OPTIONS --exact-split --safe #-}
module QuantumCat.MonoidObject where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.Category using (Category)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)

{-
Monoid object in monoidal category

   associativity:

             mul⊗id         mul
   (A⊗A)⊗A --------> A⊗A -----> A
     |
     | associator
     |
     \/      id⊗mul         mul
   A⊗(A⊗A) --------> A⊗A ------> A

   unitality:
   
         unit⊗id        mul
   I⊗A -----------> A⊗A -------> A
          left-unitor
   I⊗A --------------> A

         id⊗unit            mul
   A⊗1 -------------> A⊗A -------> A
         right-unitor
   A⊗1 --------------> A


https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
-}
record MonoidObject
    {u w : Universe}
    {C : Category u w}
    (MC : MonoidalCategory C)
    (A : Category.Obj C)
    : Type (usuc (u umax w)) where
  open MonoidalCategory MC
  open Category C

  field
    -- operations
    unit : I => A        -- create
    mul  : (A ⊗O A) => A -- merge

  -- monoid object laws - helpers
  assoc-left : ((A ⊗O A) ⊗O A) => A
  assoc-left = (mul ⊗H id) >>> mul

  assoc-right : ((A ⊗O A) ⊗O A) => A
  assoc-right = a >>> (id ⊗H mul) >>> mul

  left-unit-path : (I ⊗O A) => A
  left-unit-path = (unit ⊗H id) >>> mul

  right-unit-path : (A ⊗O I) => A
  right-unit-path = (id ⊗H unit) >>> mul

  field
    -- laws
    assoc-law : assoc-left ≡ assoc-right
    left-unit-law : left-unit-path ≡ l
    right-unit-law : right-unit-path ≡ r
