{-# OPTIONS --type-in-type #-}
module lib.Pullback where

open import lib.Category
open import lib.Utils
open Cat

record Pullback {C : Cat}{X Y Z : Obj C}
                (f : Hom C X Y)(g : Hom C Z Y) : Set where
  field P : Obj C
        p : Hom C P X
        q : Hom C P Z
        law1 : comp C f p ≡ comp C g q
        law2 : ∀{P'}(p' : Hom C P' X)(q' : Hom C P' Z) → 
               comp C f p' ≡ comp C g q' → !Hom C P' P

SetHasPullbacks : {X Y Z : Set}(f : X → Y)(g : Z → Y) → 
                  Pullback {Sets} f g
SetHasPullbacks f g = {!!}