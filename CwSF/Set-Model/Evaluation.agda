{-# OPTIONS --type-in-type #-}
module CwSF.Set-Model.Evaluation where

open import lib.Utils
open import CwSF.Set-Model.Syntax

-- interpretation of types

Val : Ty → Set
Val ι       = One
Val (σ ⇒ τ) = Val σ → Val τ

-- interpretation of contexts

Env : Con → Set
Env Γ = ∀{σ} →  Var Γ σ → Val σ

_<<_ : ∀{Γ σ} → Env Γ → Val σ → Env (Γ < σ)
(γ << v) vz     = v
(γ << v) (vs x) = γ x

-- intepretation of terms

eval : ∀{Γ σ} → Env Γ → Tm Γ σ → Val σ
eval γ (var x)   = γ x
eval γ (app t u) = eval γ t (eval γ u)
eval γ (lam t)   = λ v → eval (γ << v) t
