{-# OPTIONS --type-in-type #-}
module CwA.CwA where

open import lib.Category
open import lib.Functor
open import lib.Utils
open import lib.Pullback

record CwA : Set where
  field C : Cat
        Ty : Fun (C op) Sets
        _<_ : (Γ : Obj C) → OMap Ty Γ → Obj C
        p' : ∀{Γ}(σ : OMap Ty Γ) → Hom C (Γ < σ) Γ
        sub : ∀{B Γ}(f : Hom C B Γ)(σ : OMap Ty Γ) → 
              Σ (Pullback {C}{B}{Γ}{Γ < σ} f (p' σ)) λ pb → let open Pullback pb in {!p!}