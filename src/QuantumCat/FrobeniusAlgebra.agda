{-# OPTIONS --exact-split --safe #-}
module QuantumCat.FrobeniusAlgebra where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)
open import QuantumCat.Category using (Category)

{-
A Frobenius algebra in a monoidal category (C,x,1) consists of:
* an object A
* morphisms
 * unit u: 1 -> A
 * counit cu: A -> 1
 * multiplication: m: A x A -> A
 * comultiplication: cm: A -> A x A
such that:
 1. (A,m,u) is a monoid (associative unital algebra)
    https://ncatlab.org/nlab/show/associative+unital+algebra#OverMonoidsInAMonoidalCategory

   associativity:

             merge⊗id         merge
   (A⊗A)⊗A ------------> A⊗A ------> A
     |
     | associator
     |
     \/       id⊗merge         merge
   A⊗(A⊗A) ------------> A⊗A ------> A

   unitality:
   
         create⊗id        merge
   I⊗A -----------> A⊗A -------> A
          left-unitor
   I⊗A --------------> A

         id⊗create          merge
   A⊗1 -------------> A⊗A -------> A
         right-unitor
   A⊗1 --------------> A

 2. (A,cm,cu) is a comonoid
 3. the Frobenius laws hold:

       copy⊗id             a             id⊗merge
  A⊗A ---------> (A⊗A)⊗A --> A⊗(A⊗A) -----------> A⊗A
  
        copy            merge
  A⊗A ------> A⊗(A⊗A)------> A⊗A

        id⊗copy            a-1               merge⊗id
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
    create : I => A         -- unit
    merge  : (A ⊗O A) => A -- multiplication
    delete : A => I         -- counit
    copy   : A => (A ⊗O A) -- comultiplication

  -- monoid object laws - helpers
  monoid-assoc-left : ((A ⊗O A) ⊗O A) => A
  monoid-assoc-left = (merge ⊗H id) >>> merge
  
  monoid-assoc-right : ((A ⊗O A) ⊗O A) => A
  monoid-assoc-right = a >>> (id ⊗H merge) >>> merge

  monoid-left-unit-path : (I ⊗O A) => A
  monoid-left-unit-path = (create ⊗H id) >>> merge

  monoid-right-unit-path : (A ⊗O I) => A
  monoid-right-unit-path = (id ⊗H create) >>> merge

  field
    -- monoid object diagrams
    monoid-assoc-law : monoid-assoc-left ≡ monoid-assoc-right
    monoid-left-unit-law : monoid-left-unit-path ≡ l
    monoid-right-unit-law : monoid-right-unit-path ≡ r

  -- comonoid object laws - helpers
  comonoid-coassoc-left : A => (A ⊗O (A ⊗O A))
  comonoid-coassoc-left = copy >>> (copy ⊗H id{A}) >>> a{A}{A}{A}

  comonoid-coassoc-right : A => (A ⊗O (A ⊗O A))
  comonoid-coassoc-right = copy >>> (id{A} ⊗H copy)

  comonoid-left-counit-path : A => A
  comonoid-left-counit-path = copy >>> (delete ⊗H id) >>> l

  comonoid-right-counit-path : A => A
  comonoid-right-counit-path = copy >>> (id ⊗H delete) >>> r

  field
    -- comonoid objectlaws diagrams
    comonoid-assoc-law : comonoid-coassoc-left ≡ comonoid-coassoc-right
    comonoid-left-counit-law : comonoid-left-counit-path ≡ id
    comonoid-right-counit-law : comonoid-right-counit-path ≡ id

  -- Frobenius law - helpers
  frobenius-middle : (A ⊗O A) => (A ⊗O A)
  frobenius-middle = merge >>> copy

  frobenius-left : (A ⊗O A) => (A ⊗O A)
  frobenius-left = (copy ⊗H id) >>> a >>> (id ⊗H merge)

  frobenius-right : (A ⊗O A) => (A ⊗O A)
  frobenius-right = (id ⊗H copy) >>> a⁻¹ >>> (merge ⊗H id)

  field
    -- Frobenius law - diagrams
    frobenius-law-left : frobenius-left ≡ frobenius-middle
    frobenius-law-right : frobenius-right ≡ frobenius-middle
 
