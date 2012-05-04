module E2-4-andri where

data ℕ : Set where -- N-F
  Zero : ℕ         -- N-I-0
  Suc : ℕ → ℕ      -- N-I-S

R-ℕ : (σ : ℕ → Set)
      (Hz : σ Zero)
      (Hs : (n : ℕ)(x : σ n) → σ (Suc n))
      (M : ℕ) →
      σ M          -- N-E
R-ℕ σ Hz Hs Zero = Hz
R-ℕ σ Hz Hs (Suc M) = Hs M (R-ℕ σ Hz Hs M)

_+_ : ℕ → ℕ → ℕ
m + n = R-ℕ (λ _ → ℕ → ℕ) (λ x → x) (λ _ ih → λ n → Suc (ih n)) m n

data Bin : ℕ → Set where
  Zero : Bin (Suc Zero)
  Suc₀ : ∀{n} → Bin n → Bin (n + n)
  Suc₁ : ∀{n} → Bin n → Bin (n + n)

R-Bin : (σ : (n : ℕ) → Bin n → Set)
        (Hz : σ (Suc Zero) Zero)
        (Hs₀ : (m : ℕ)(n : Bin m)(x : σ m n) → σ (m + m) (Suc₀ n))
        (Hs₁ : (m : ℕ)(n : Bin m)(x : σ m n) → σ (m + m) (Suc₁ n))
        {n : ℕ} (M : Bin n) →
        σ n M
R-Bin σ Hz Hs₀ Hs₁ Zero = Hz
R-Bin σ Hz Hs₀ Hs₁ (Suc₀ n) = Hs₀ _ n (R-Bin σ Hz Hs₀ Hs₁ n)
R-Bin σ Hz Hs₀ Hs₁ (Suc₁ n) = Hs₁ _ n (R-Bin σ Hz Hs₀ Hs₁ n) 

E2-4 : ∀{n} → Bin n → ℕ
E2-4 n = R-Bin (λ _ _ → ℕ) Zero (λ _ _ ih₀ → ih₀) (λ m _ ih₁ → m + ih₁) n