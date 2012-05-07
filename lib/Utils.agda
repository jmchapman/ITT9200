module lib.Utils where

data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

infix 10 _≡_

id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → 
      (Y → Z) → (X → Y) → X → Z
(f ∘ g) x = f (g x)

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst