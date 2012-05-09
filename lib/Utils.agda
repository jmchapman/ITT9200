module lib.Utils where


-- functions
id : {X : Set} → X → X
id x = x

_∘_ : {X Y Z : Set} → 
      (Y → Z) → (X → Y) → X → Z
(f ∘ g) x = f (g x)

-- equality
data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

infix 10 _≡_

postulate ext  : {X Y : Set}{f g : X → Y} → (∀ x → f x ≡ g x) → f ≡ g
postulate iext : {X : Set}{Y : X → Set}{f g : {x : X} → Y x} → 
                 (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

sym : {X : Set}{x x' : X} → x ≡ x' → x' ≡ x
sym refl = refl

trans : {X : Set}{x x' x'' : X} → x ≡ x' → x' ≡ x'' → x ≡ x''
trans refl p = p

cong : {X Y : Set}(f : X → Y){x x' : X} → x ≡ x' → f x ≡ f x'
cong f refl = refl

cong2 : {X Y Z : Set}(f : X → Y → Z){x x' : X} → x ≡ x' → {y y' : Y} → y ≡ y' → f x y ≡ f x' y'
cong2 f refl refl = refl

-- pairs
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst