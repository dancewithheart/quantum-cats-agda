module QuantumCat.Iso where

open import QuantumCat.Common using (Type; Universe)
open import QuantumCat.Category using (Category)
open import Agda.Builtin.Equality using (_≡_)

record Iso
    {u w : Universe}
    (C : Category u w)
    (A B : Category.Obj C)
    : Type w where

  open Category C

  field
    to   : Hom A B
    from : Hom B A
    to-from : to >>> from ≡ id {A}
    from-to : from >>> to ≡ id {B}
 
