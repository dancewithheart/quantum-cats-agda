{-# OPTIONS --exact-split --safe #-}
module QuantumCat.CompactClosedCategory where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; _umax_; usuc)
open import QuantumCat.Category using (Category)
open import QuantumCat.Iso using (Iso)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)
open import QuantumCat.BraidedMonoidalCategory using (BraidedMonoidalCategory)
open import QuantumCat.SymmetricMonoidalCategory using (SymmetricMonoidalCategory)

{-
Compact closed category

https://math.ucr.edu/home/baez/act_course/lecture_74.html

https://ncatlab.org/nlab/show/compact+closed+category
-}

record CompactClosedCategory
    {u w : Universe}
    {C : Category u w}
    {MC : MonoidalCategory C}
    {BMC : BraidedMonoidalCategory MC}
    (SMC : SymmetricMonoidalCategory BMC)
    : Type (usuc (u umax w)) where
  open MonoidalCategory MC
  open Category C
  open Iso
  field
    dual : Obj -> Obj

    unit : {A : Obj} -> I => (dual A ⊗O A) -- coevaluation/unit
    counit : {A : Obj} -> (A ⊗O dual A) => I -- evaluation/counit

    yanking-left : {A : Obj} -> (r⁻¹{A}
      >>> (id{A} ⊗H unit{A})
      >>> a⁻¹{A}{dual A}{A}
      >>> (counit{A} ⊗H id{A})
      >>> l{A})
       ≡ id{A}
    yanking-right : {A : Obj} -> (l⁻¹{dual A}
      >>> (unit{A} ⊗H id{dual A})
      >>> a{dual A}{A}{dual A}
      >>> (id{dual A} ⊗H counit{A})
      >>> r{dual A})
       ≡ id{dual A}
