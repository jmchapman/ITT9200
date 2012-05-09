{-# OPTIONS --type-in-type #-}
module CwSF.Set-Model.Syntax where

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _<_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀{Γ σ} → Var (Γ < σ) σ
  vs : ∀{Γ σ τ} → Var Γ σ → Var (Γ < τ) σ

data Tm : Con → Ty → Set where
  var : ∀{Γ σ} → Var Γ σ → Tm Γ σ
  app : ∀{Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ
  lam : ∀{Γ σ τ} → Tm (Γ < σ) τ → Tm Γ (σ ⇒ τ)
