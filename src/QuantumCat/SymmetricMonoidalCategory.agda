{-# OPTIONS --exact-split --safe #-}
module QuantumCat.SymmetricMonoidalCategory where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; _umax_; usuc)
open import QuantumCat.Category using (Category)
open import QuantumCat.Iso using (Iso)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)
open import QuantumCat.BraidedMonoidalCategory using (BraidedMonoidalCategory)

{-
https://ncatlab.org/nlab/show/symmetric+monoidal+category
-}
record SymmetricMonoidalCategory
    {u w : Universe}
    {C : Category u w}
    {MC : MonoidalCategory C}
    (BMC : BraidedMonoidalCategory MC) : Type (usuc (u umax w)) where
  open BraidedMonoidalCategory BMC
  open Category C
  field
    symmetry : {X Y : Obj} -> (β{X}{Y} >>> β{Y}{X}) ≡ id
