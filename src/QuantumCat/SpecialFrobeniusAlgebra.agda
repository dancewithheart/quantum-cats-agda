{-# OPTIONS --exact-split --safe #-}
module QuantumCat.SpecialFrobeniusAlgebra where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)
open import QuantumCat.ComonoidObject using (ComonoidObject)
open import QuantumCat.MonoidObject using (MonoidObject)
open import QuantumCat.FrobeniusAlgebra using (FrobeniusAlgebra)
open import QuantumCat.Category using (Category)

record SpecialFrobeniusAlgebra
    {u w : Universe}
    {C : Category u w}
    {MC : MonoidalCategory C}
    (FA : FrobeniusAlgebra MC) : Type (usuc (u umax w)) where
  open FrobeniusAlgebra FA
  open Category C
  open ComonoidObject comonoid
  open MonoidObject monoid
  field
    special-law : comul >>> mul ≡ id{A}

