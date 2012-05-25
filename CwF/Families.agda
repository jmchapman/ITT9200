{-# OPTIONS --type-in-type #-}
module CwF.Families where

open import lib.Category
open import lib.Utils
Fam : Cat
Fam = record {
  Obj  = Σ Set λ B → B → Set;
  Hom  = λ B C → Σ (fst B → fst C) λ f → ∀ {b} → snd B b → snd C (f b);
  iden = id , id;
  comp = λ f g → (fst f ∘ fst g) , (snd f ∘ snd g);
  idl  = refl;
  idr  = refl;
  ass  = refl}