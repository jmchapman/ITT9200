{-# OPTIONS --type-in-type #-}
module CwSF.Set-Model.Renaming where

open import CwSF.Set-Model.Syntax
open import lib.Utils
open import lib.Category

Ren : Con → Con → Set
Ren Γ Δ = ∀ {σ} → Var Γ σ → Var Δ σ 

renId : ∀{Γ} → Ren Γ Γ
renId = id

renComp : ∀{B Γ Δ} → Ren Γ Δ → Ren B Γ → Ren B Δ
renComp f g = f ∘ g

ConCat : Cat 
ConCat = record{
  Obj  = Con; 
  Hom  = Ren;
  iden = renId;
  comp = renComp;
  idl  = iext λ _ → refl;
  idr  = iext λ _ → refl;
  ass  = iext λ _ → refl}

wk : ∀{Γ Δ σ} → Ren Γ Δ → Ren (Γ < σ) (Δ < σ)
wk f vz     = vz
wk f (vs i) = vs (f i)

ren : ∀{Γ Δ} → Ren Γ Δ → ∀ {σ} → Tm Γ σ → Tm Δ σ
ren f (var x)   = var (f x)
ren f (app t u) = app (ren f t) (ren f u)
ren f (lam t)   = lam (ren (wk f) t)

wkid : ∀{Γ σ τ}(x : Var (Γ < τ) σ) → wk renId x ≡ renId x
wkid vz     = refl
wkid (vs x) = refl

renid : ∀{Γ σ}(t : Tm Γ σ) → ren renId t ≡ id t
renid (var x)   = refl
renid (app t u) = cong2 app (renid t) (renid u)
renid (lam t) = cong lam (trans (cong (λ (f : Ren _ _) → ren f t) 
                                      (iext (λ _ → ext wkid))) 
                                (renid t))

wkcomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) → 
            wk (renComp f g) x ≡ renComp (wk f) (wk g) x  
wkcomp f g vz     = refl
wkcomp f g (vs i) = refl

rencomp : ∀ {B Γ Δ}(f : Ren Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
            ren (renComp f g) t ≡ (ren f ∘ ren g) t
rencomp f g (var x)   = refl
rencomp f g (app t u) = cong2 app (rencomp f g t) (rencomp f g u)
rencomp f g (lam t)   = cong lam (trans (cong (λ (f : Ren _ _) → ren f t)
                                              (iext λ _ → ext (wkcomp f g)))
                                        (rencomp (wk f) (wk g) t))

