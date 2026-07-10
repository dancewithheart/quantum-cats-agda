{-# OPTIONS --exact-split --safe #-}
module QuantumCat.ComonoidObject where

open import Agda.Builtin.Equality using (_≡_)
open import QuantumCat.Common using (Type; Universe; usuc; _umax_)
open import QuantumCat.Category using (Category)
open import QuantumCat.MonoidalCategory using (MonoidalCategory)

record ComonoidObject
    {u w : Universe}
    {C : Category u w}
    (MC : MonoidalCategory C)
    (A : Category.Obj C)
    : Type (usuc (u umax w)) where
  open MonoidalCategory MC
  open Category C
  field
    -- operations
    counit : A => I
    comul  : A => (A ⊗O A)

  -- helpers for laws
  coassoc-left : A => (A ⊗O (A ⊗O A))
  coassoc-left = comul >>> (comul ⊗H id{A}) >>> a{A}{A}{A}

  coassoc-right : A => (A ⊗O (A ⊗O A))
  coassoc-right = comul >>> (id{A} ⊗H comul)

  left-counit-path : A => A
  left-counit-path = comul >>> (counit ⊗H id) >>> l

  right-counit-path : A => A
  right-counit-path = comul >>> (id ⊗H counit) >>> r

  field
    -- comonoid objectlaws laws
    coassoc-law : coassoc-left ≡ coassoc-right
    left-counit-law : left-counit-path ≡ id
    right-counit-law : right-counit-path ≡ id
