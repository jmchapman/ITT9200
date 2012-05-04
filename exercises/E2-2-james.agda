module E2-2-james where

data Σ (σ : Set)(τ : σ → Set) : Set where
  Pair : (x : σ) → τ x → Σ σ τ

fst : {σ : Set}{τ : σ → Set} → Σ σ τ → σ
fst (Pair a b) = a

snd : {σ : Set}{τ : σ → Set}(p : Σ σ τ) → τ (fst p)
snd (Pair a b) = b

E2-2 : {σ τ : Set}{ρ : σ → τ → Set} → ((x : σ) → Σ τ (ρ x)) →  
       Σ (σ → τ) (λ f → (x : σ) → ρ x (f x))
E2-2 f = Pair (λ x → fst (f x)) (λ x → snd (f x))
