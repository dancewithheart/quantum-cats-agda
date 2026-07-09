{-# OPTIONS --exact-split --safe #-}
module QuantumCat.ProductCategory where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong₂)
open import Data.Product using (_×_; _,_) renaming (proj₁ to fst; proj₂ to snd)
open import QuantumCat.Common using (Universe; _umax_)
open import QuantumCat.Category using (Category)

{-
Product category

https://ncatlab.org/nlab/show/product+category
-}
ProductCategory : {uC uD wC wD : Universe} ->
  Category uC wC ->
  Category uD wD ->
  Category (uC umax uD) (wC umax wD)
ProductCategory C D = record
  { Obj   = C.Obj × D.Obj
  ; _=>_  = \X Y -> (fst X) C.=> (fst Y) × (snd X) D.=> (snd Y)
  ; id    = (C.id , D.id)
  ; _>>>_ = \f g -> (fst f C.>>> fst g , (snd f D.>>> snd g))
  ; cat-left-id       = \f -> cong₂ _,_ (C.cat-left-id (fst f)) (D.cat-left-id (snd f))
  ; cat-right-id      = \f -> cong₂ _,_ (C.cat-right-id (fst f)) (D.cat-right-id (snd f)) 
  ; cat-assoc = \f g h -> cong₂
     _,_
     (C.cat-assoc (fst f) (fst g) (fst h))
     (D.cat-assoc (snd f) (snd g) (snd h)) 
  }
  where
    module C = Category C
    module D = Category D
