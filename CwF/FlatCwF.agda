{-# OPTIONS --type-in-type #-}
module CwF.FlatCwF where

open import lib.Utils
open import lib.Category
open Cat

record FlatCwF : Set where
  field C         : Cat
        Ty        : Obj C → Set
        Tm        : (Γ : Obj C) → Ty Γ → Set
        _[_]⁺     : {Γ Δ : Obj C} → Ty Δ → Hom C Γ Δ → Ty Γ
        _[_]      : {Γ Δ : Obj C} → {σ : Ty Δ} → Tm Δ σ → (f : Hom C Γ Δ) → Tm Γ (σ [ f ]⁺)
        Ty-Id     : ∀{Θ}{σ : Ty Θ} → σ [ iden C ]⁺ ≅ σ
        Ty-Comp   : ∀{Γ Δ Θ}{f : Hom C Γ Δ}{g : Hom C Δ Θ}{σ : Ty Θ} → 
                    σ [ comp C g f ]⁺ ≅ σ [ g ]⁺ [ f ]⁺
        Tm-Id     : ∀{Θ σ}{M : Tm Θ σ} → M [ iden C ] ≅ M
        Tm-Comp   : ∀{Γ Δ Θ σ}{M : Tm Θ σ}{f : Hom C Γ Δ}{g : Hom C Δ Θ} →
                    M [ comp C g f ] ≅ M [ g ] [ f ]
        ε         : Obj C
        []        : {Γ : Obj C} → !Hom C Γ ε
        _<_       : (Γ : Obj C) → Ty Γ → Obj C
        p         : {Γ : Obj C} → (σ : Ty Γ) → Hom C (Γ < σ) Γ
        v         : {Γ : Obj C}{σ : Ty Γ} → Tm (Γ < σ) (σ [ p σ ]⁺)
        _<<_      : ∀{Γ Δ σ} → (f : Hom C Γ Δ) → Tm Γ (σ [ f ]⁺) → Hom C Γ (Δ < σ)
        Cons-L    : ∀{Γ Δ σ}{f : Hom C Γ Δ}{M : Tm Γ (σ [ f ]⁺)} → 
                    comp C (p σ) (f << M) ≅ f
        Cons-R    : ∀{Γ Δ σ}{f : Hom C Γ Δ}{M : Tm Γ (σ [ f ]⁺)} → v [ f << M ] ≅ M
        Cons-Nat  : ∀{B Γ Δ σ}{f : Hom C Γ Δ}{g : Hom C B Γ}{M : Tm Γ (σ [ f ]⁺)} → 
                    comp C (f << M) g ≅ comp C f g << subst' (Tm B) (sym' Ty-Comp) (M [ g ])
        Cons-Id   : ∀{Δ σ} → (p σ) << v ≅ iden C {Δ < σ}
  -- weakening from Section 3.1.3
  q : ∀{B Γ} → (f : Hom C B Γ) → (σ : Ty Γ) → Hom C (B < (σ [ f ]⁺)) (Γ < σ) 
  q f σ = comp C f (p (σ [ f ]⁺)) << subst' (Tm _) (sym' Ty-Comp) v  

  E3-4-1 : ∀{Γ}{σ : Ty Γ} → q (iden C) σ ≅ iden C {Γ < σ}
  E3-4-1 {Γ} {σ} = trans' (cong5' (λ Γ Δ σ → _<<_ {Γ} {Δ} {σ}) 
                                  (cong' (_<_ Γ) Ty-Id) 
                                  refl 
                                  refl
                                  (trans' (≡-to-≅ (idl C)) (cong' p Ty-Id))
                                  (trans' (subst'-removable (Tm (Γ < (σ [ iden C ]⁺))) (sym' Ty-Comp) v) (cong' (λ σ → v {σ = σ}) Ty-Id)))
                          Cons-Id

  E3-4-2 : ∀{Γ Δ Θ}{σ : Ty Θ}{f : Hom C Δ Θ}{g : Hom C Γ Δ} → q (comp C f g) σ ≅ comp C (q f σ)  (q g (σ [ f ]⁺))
  E3-4-2 = {!!}

