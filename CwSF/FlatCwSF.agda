{-# OPTIONS --type-in-type #-}
module CwSF.FlatCwSF where

open import lib.Utils
open import lib.Category
open Cat

record FlatCwSF : Set where
  field C         : Cat
        Ty        : Set
        Tm        : Obj C → Ty → Set
        _[_]      : {Γ Δ : Obj C} → 
                    {σ : Ty} → Tm Δ σ → Hom C Γ Δ → Tm Γ σ 
        Tm-Id     : ∀{σ}{Θ}{M : Tm Θ σ} → M [ iden C ] ≡ M
        Tm-Comp   : ∀{σ}{Γ Δ Θ}
                    {M : Tm Θ σ}{f : Hom C Γ Δ}{g : Hom C Δ Θ} →
                    M [ comp C g f ] ≡ M [ g ] [ f ]
        ε         : Obj C
        []        : {Γ : Obj C} → !Hom C Γ ε
        _<_       : (Γ : Obj C) → Ty → Obj C
        p         : {Γ : Obj C}{σ : Ty} → Hom C (Γ < σ) Γ
        v         : {Γ : Obj C}{σ : Ty} → Tm (Γ < σ) σ
        _<<_      : ∀{Γ Δ σ} → 
                    Hom C Γ Δ → Tm Γ σ → Hom C Γ (Δ < σ)
        Cons-L    : ∀{Γ Δ σ}{f : Hom C Γ Δ}{M : Tm Γ σ} → 
                    comp C p (f << M) ≡ f
        Cons-R    : ∀{Γ Δ σ}{f : Hom C Γ Δ}{M : Tm Γ σ} → 
                    v [ f << M ] ≡ M
        Cons-Nat  : ∀{B Γ Δ σ}
                    {f : Hom C Γ Δ}{g : Hom C B Γ}{M : Tm Γ σ} → 
                    comp C (f << M) g ≡ comp C f g << M [ g ]
        Cons-Id   : ∀{Δ σ}{M : Tm Δ σ} → p << v ≡ iden C {Δ < σ}