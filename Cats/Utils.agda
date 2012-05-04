module Utils where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

