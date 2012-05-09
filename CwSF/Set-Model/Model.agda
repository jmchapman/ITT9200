{-# OPTIONS --type-in-type #-}
module CwSF.Set-Model.Model where

open import lib.Utils
open import lib.Category
open import CwSF.Set-Model.Syntax
open import CwSF.Set-Model.Evaluation
open import CwSF.FlatCwSF

Set-Model : FlatCwSF
Set-Model = record {
              C        = Sets;
              Ty       = Set;
              Tm       = λ Γ σ  → Γ → σ ;
              _[_]     = _∘_;
              Tm-Id    = refl;
              Tm-Comp  = refl;
              ε        = One;
              []       = (λ _ → void) , (λ g → ext λ _ → refl);
              _<_      = _×_ ;
              p        = fst;
              v        = snd;
              _<<_     = λ f g x → f x , g x;
              Cons-L   = refl;
              Cons-R   = refl;
              Cons-Nat = refl;
              Cons-Id  = refl }