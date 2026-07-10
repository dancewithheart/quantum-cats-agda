{-# OPTIONS --exact-split --safe #-}
module QuantumCat.FrobeniusAlgebra where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)
open import QuantumCat.MonoidObject using (MonoidObject)
open import QuantumCat.ComonoidObject using (ComonoidObject)
open import QuantumCat.Category using (Category)

{-
A Frobenius algebra in a monoidal category (C,x,1) consists of:
* an object A
* morphisms
 * unit: 1 -> A
 * multiplication: A x A -> A
 * counit: A -> 1
 * comultiplication: A -> A x A
such that:
 1. (A,mul,unit) is a monoid object (associative unital algebra)
 2. (A,comul,counit) is a comonoid object (coassociative counital algebra)
 3. the Frobenius laws hold:

       comul⊗id             a             id⊗mul
  A⊗A ---------> (A⊗A)⊗A --> A⊗(A⊗A) -----------> A⊗A
  
        comul            mul
  A⊗A ------> A⊗(A⊗A)------> A⊗A

        id⊗comul            a-1               mul⊗id
  A⊗A ---------->A⊗(A⊗A) ------> (A⊗A)⊗A ----------> A⊗A
  

https://ncatlab.org/nlab/show/Frobenius+algebra
-}
record FrobeniusAlgebra
    {u w : Universe}
    {C : Category u w}
    (MC : MonoidalCategory C) : Type (usuc (u umax w)) where
  open MonoidalCategory MC
  open Category C
  field
    A      : Obj
    monoid   : MonoidObject MC A
    comonoid : ComonoidObject MC A

  open MonoidObject monoid
  open ComonoidObject comonoid
  -- Frobenius law - helpers
  frobenius-middle : (A ⊗O A) => (A ⊗O A)
  frobenius-middle = mul >>> comul

  frobenius-left : (A ⊗O A) => (A ⊗O A)
  frobenius-left = (comul ⊗H id) >>> a >>> (id ⊗H mul)

  frobenius-right : (A ⊗O A) => (A ⊗O A)
  frobenius-right = (id ⊗H comul) >>> a⁻¹ >>> (mul ⊗H id)

  field
    -- Frobenius law - diagrams
    frobenius-law-left : frobenius-left ≡ frobenius-middle
    frobenius-law-right : frobenius-right ≡ frobenius-middle
