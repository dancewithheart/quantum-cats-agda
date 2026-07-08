{-# OPTIONS --exact-split --safe #-}
module QuantumCat.Common where

open import Agda.Primitive public renaming
  ( Level to Universe -- HoTT terminology
  ; Set to Type       -- HoTT/FP terminology
  ; lzero to u0
  ; lsuc to usuc      -- next universe
  ; _⊔_ to _umax_     -- max of 2 universes
  )

variable l u w z : Universe
