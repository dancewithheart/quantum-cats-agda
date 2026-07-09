module QuantumCat.Iso where

open import QuantumCat.Common using (Type; Universe)
open import QuantumCat.Category using (Category)
open import Agda.Builtin.Equality using (_≡_)

{-
Isomorphism in a category

https://ncatlab.org/nlab/show/isomorphism

ACT Course - Lecture 46 - Isomorphisms - John Baez
https://math.ucr.edu/home/baez/act_course/lecture_46.html
-}
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
 
