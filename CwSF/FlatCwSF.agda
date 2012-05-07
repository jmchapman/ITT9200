{-# OPTIONS --type-in-type #-}
module CwSF.FlatCwSF where

open import Cats.Utils
open import Cats.Category
open Cat

record FlatCwSF : Set where
  field C : Cat
        Ty : Set
        Tm : Obj C → Ty → Set
        _[_] : {Γ Δ : Obj C} → Hom C Γ Δ → {σ : Ty} → Tm Δ σ → Tm Γ σ 