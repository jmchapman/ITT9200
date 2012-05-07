module Cats.Utils where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → 
      (Y → Z) → (X → Y) → X → Z
(f ∘ g) x = f (g x)