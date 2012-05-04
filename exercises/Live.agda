module Live where

data ℕ : Set where  
  Zero : ℕ
  Suc  : ℕ → ℕ

R-ℕ : (σ : ℕ → Set)
      (Hz : σ Zero)
      (Hs : (n : ℕ) → σ n → σ (Suc n))
      (M : ℕ) → σ M
R-ℕ σ Hz Hs Zero    = Hz
R-ℕ σ Hz Hs (Suc M) = Hs M (R-ℕ σ Hz Hs M)

{-
_+_ Zero = λ n → n
_+_ (Suc m) = λ n → Suc ((_+_ m) n)
-}

_+_ : ℕ → (ℕ → ℕ)
_+_ m = R-ℕ (λ _ → ℕ → ℕ) (λ x → x) (λ _ ih → λ n → Suc (ih n)) m

data Id {σ : Set} : σ → σ → Set where
  Refl : (M : σ) → Id M M

R-Id : {σ : Set}
       (τ : (x y : σ) → Id x y → Set)
       (H : (z : σ) → τ z z (Refl z))
       (M N : σ)(P : Id M N) → τ M N P
R-Id τ H .N N (Refl .N) = H N 


Subst : {σ : Set}(P : σ → Set)(x y : σ) → Id x y → P x → P y
Subst P x y p = R-Id (λ x y _ → P x → P y) (λ _ p → p) x y p

Resp : {σ τ : Set}(U : σ → τ)(M N : σ) → Id M N → Id (U M) (U N)
Resp U M N P = Subst (λ x → Id (U M) (U x)) M N P (Refl (U M))

Trans : {σ : Set}(x y z : σ) → Id x y → Id y z → Id x z
Trans x y z p q = R-Id (λ x y p₁ → Id y z → Id x z) (λ _ p → p) x y p q


E2-1-lem0 : ∀ n → Id (Zero + n) (n + Zero)
E2-1-lem0 n = R-ℕ (λ n₁ → Id (Zero + n₁) (n₁ + Zero))
                  (Refl Zero)
                  (λ n p → Resp Suc _ _ p)
                  n

E2-1-lem1 : ∀ m n → Id (Suc m + n) (m + Suc n)
E2-1-lem1 = {!!}

E2-1 : ∀ m n → Id (m + n) (n + m)
E2-1 m n = R-ℕ (λ m → Id (m + n) (n + m))
             (E2-1-lem0 n)
             (λ m' p → Trans _ _ _ (Resp Suc _ _ p) (E2-1-lem1 n m'))
             m

data Σ (σ : Set)(τ : σ → Set) : Set where
  Pair : (x : σ) → τ x → Σ σ τ

fst : {σ : Set}{τ : σ → Set} → Σ σ τ → σ
fst (Pair a b) = a

snd : {σ : Set}{τ : σ → Set}(p : Σ σ τ) → τ (fst p)
snd (Pair a b) = b

E2-2 : {σ τ : Set}{ρ : σ → τ → Set} → ((x : σ) → Σ τ (ρ x)) →  
       Σ (σ → τ) (λ f → (x : σ) → ρ x (f x))
E2-2 f = Pair (λ x → fst (f x)) (λ x → snd (f x))
