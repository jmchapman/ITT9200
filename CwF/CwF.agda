{-# OPTIONS --type-in-type #-}
module CwF.CwF where

open import CwF.Families
open import lib.Category
open import lib.Functor
open import lib.Utils

record Cmpr {C : Cat}{F : Fun (C op) Fam}(Γ : Obj C)(σ : fst (OMap F Γ)) : Set
  where
  -- some useful synomyms
  Ty : Obj C → Set
  Ty = fst ∘ OMap F
  Tm : (Γ : Obj C) → Ty Γ → Set
  Tm = snd ∘ OMap F
  _[_]⁺ : ∀{Γ Δ} → Ty Δ → Hom C Γ Δ → Ty Γ
  _[_]⁺ τ f = fst (HMap F f) τ
  _[_] : ∀{Γ Δ}{σ : Ty Δ} →  Tm Δ σ → (f : Hom C Γ Δ) → Tm Γ (σ [ f ]⁺)
  _[_] t f = snd (HMap F f) t

  field Γ, : Obj C
        p  : Hom C Γ, Γ
        v  : Tm Γ, (σ [ p ]⁺)
        _<<_ : ∀{Δ}(f : Hom C Δ Γ)(M : Tm Δ (σ [ f ]⁺)) → 
               Σ (!Hom C Δ Γ,) 
                 λ !<f,M> → (comp C p (fst !<f,M>) ≅ f) 
                            × 
                            (v [ fst !<f,M> ] ≅ M)


record CwF : Set where
  field C    : Cat
        F    : Fun (C op) Fam
        cmpr : ∀ Γ σ → Cmpr {C}{F} Γ σ