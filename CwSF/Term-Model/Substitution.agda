{-# OPTIONS --type-in-type #-}
module CwSF.Set-Model.Substitution where

open import CwSF.Set-Model.Syntax
open import CwSF.Set-Model.Renaming
open import lib.Utils

Sub : Con → Con → Set
Sub Γ Δ = ∀{σ} → Var Γ σ → Tm Δ σ

lift : ∀{Γ Δ σ} → Sub Γ Δ → Sub (Γ < σ) (Δ < σ)
lift f vz     = var vz
lift f (vs x) = ren vs (f x)

sub : ∀{Γ Δ} → Sub Γ Δ → ∀{σ} → Tm Γ σ → Tm Δ σ
sub f (var x)   = f x
sub f (app t u) = app (sub f t) (sub f u)
sub f (lam t)   = lam (sub (lift f) t)

subId : ∀{Γ} → Sub Γ Γ
subId = var

subComp : ∀{B Γ Δ} → Sub Γ Δ → Sub B Γ → Sub B Δ
subComp f g = sub f ∘ g

liftid : ∀{Γ σ τ}(x : Var (Γ < σ) τ) → lift subId x ≡ subId x
liftid vz     = refl
liftid (vs x) = refl

subid : ∀{Γ σ}(t : Tm Γ σ) → sub subId t ≡ id t
subid (var x)   = refl
subid (app t u) = cong2 app (subid t) (subid u)
subid (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                        (iext λ _ → ext liftid)) 
                                  (subid t))

-- time for the mysterious four lemmas:
liftwk : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ τ}(x : Var (B < σ) τ) →
            (lift f ∘ wk g) x ≡ lift (f ∘ g) x
liftwk f g vz     = refl
liftwk f g (vs x) = refl

subren : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Ren B Γ){σ}(t : Tm B σ) → 
         (sub f ∘ ren g) t ≡ sub (f ∘ g) t
subren f g (var x)   = refl
subren f g (app t u) = cong2 app (subren f g t) (subren f g u)
subren f g (lam t)   = cong lam (trans (subren (lift f) (wk g) t)
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → ext (liftwk f g))))

renwklift : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
               (ren (wk f) ∘ lift g) x ≡ lift (ren f ∘ g) x
renwklift f g vz     = refl
renwklift f g (vs x) = trans (sym (rencomp (wk f) vs (g x))) 
                                (rencomp vs f (g x))

rensub : ∀{B Γ Δ}(f : Ren Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) →
         (ren f ∘ sub g) t ≡ sub (ren f ∘ g) t
rensub f g (var x)   = refl
rensub f g (app t u) = cong2 app (rensub f g t) (rensub f g u)
rensub f g (lam t)   = cong lam (trans (rensub (wk f) (lift g) t) 
                                       (cong (λ (f : Sub _ _) → sub f t) 
                                             (iext λ _ → 
                                               ext (renwklift f g))))

liftcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ τ}(x : Var (B < σ) τ) →
           lift (subComp f g) x ≡ subComp (lift f) (lift g) x
liftcomp f g vz     = refl
liftcomp f g (vs x) = trans (rensub vs f (g x))
                            (sym (subren (lift f) vs (g x)))

subcomp : ∀{B Γ Δ}(f : Sub Γ Δ)(g : Sub B Γ){σ}(t : Tm B σ) → 
          sub (subComp f g) t ≡ (sub f ∘ sub g) t
subcomp f g (var x)   = refl
subcomp f g (app t u) = cong2 app (subcomp f g t) (subcomp f g u)
subcomp f g (lam t)   = cong lam (trans (cong (λ (f : Sub _ _) → sub f t) 
                                              (iext λ _ → ext (liftcomp f g))) 
                                        (subcomp (lift f) (lift g) t))
