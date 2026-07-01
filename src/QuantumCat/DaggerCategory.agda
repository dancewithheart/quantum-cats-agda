module QuantumCat.DaggerCategory where

open import Agda.Primitive public renaming
  ( Level to Universe -- HoTT terminology
  ; Set to Type       -- HoTT/FP terminology
  ; lzero to u0
  ; lsuc to usuc      -- next universe
  ; _⊔_ to _umax_     -- max of 2 universes
  )

variable l u w z : Universe

u1 = usuc u0
  

-- https://ncatlab.org/nlab/show/dagger+category
record DaggerCategory (u w : Universe) : Type (usuc (u umax w)) where
  field
    -- types
    Obj  : Type u         -- objects
    Hom  : (source : Obj)
      -> (target : Obj)
      -> Type w           -- home object
