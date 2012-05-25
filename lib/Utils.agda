module lib.Utils where


-- functions
id : {X : Set} → X → X
id x = x

_∘_ : {X : Set}{Y : X → Set}{Z : ∀ {x} → Y x → Set} → 
      (∀{x} → (y : Y x) → Z y) → (g : ∀ x → Y x) → (∀ x → Z (g x)) 
(f ∘ g) x = f (g x)

-- equality
data _≡_ {A : Set}(a : A) : A → Set where
  refl : a ≡ a

infix 10 _≡_

postulate ext  : {X Y : Set}{f g : X → Y} → (∀ x → f x ≡ g x) → f ≡ g
postulate iext : {X : Set}{Y : X → Set}{f g : {x : X} → Y x} → 
                 (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

subst : ∀{A a b} → (P : A → Set) → a ≡ b → P a → P b
subst P refl p = p

sym : {X : Set}{x x' : X} → x ≡ x' → x' ≡ x
sym refl = refl

trans : {X : Set}{x x' x'' : X} → x ≡ x' → x' ≡ x'' → x ≡ x''
trans refl p = p

cong : ∀{X Y} → (f : X → Y) → {x x' : X} → x ≡ x' → f x ≡ f x'
cong f refl = refl

cong2 : {X Y Z : Set}(f : X → Y → Z){x x' : X} → x ≡ x' → {y y' : Y} → y ≡ y' → f x y ≡ f x' y'
cong2 f refl refl = refl


-- heterogeneous equality
data _≅_ {A : Set} (x : A) : {B : Set} → B → Set where
  refl : x ≅ x

infix 10 _≅_

subst' : ∀{A a b} → (P : A → Set) → a ≅ b → P a → P b
subst' P refl p = p

sym' : {X X' : Set}{x : X}{x' : X'} → x ≅ x' → x' ≅ x
sym' refl = refl

trans' : {X X' X'' : Set}{x : X}{x' : X'}{x'' : X''} → x ≅ x' → x' ≅ x'' → x ≅ x''
trans' refl p = p

cong' : {X : Set}{Y : X → Set} → (f : ∀ x → Y x) → {x x' : X} → x ≅ x' → f x ≅ f x'
cong' f refl = refl

cong2' : {X : Set}{Y : X → Set}{Z : ∀ x → Y x → Set}(f : ∀ x y → Z x y){x x' : X} → x ≅ x' → {y : Y x}{y' : Y x'} → y ≅ y' → f x y ≅ f x' y'
cong2' f refl refl = refl

-- you do not want to know
cong5' : {X : Set}{Y : X → Set}{Z : ∀ x → Y x → Set}{A : ∀ x y → Z x y → Set}{B : ∀ x y z → A x y z → Set}{C : ∀ x y z a → B x y z a → Set} (f : ∀ x y z a b → C x y z a b)
  {x x' : X} → x ≅ x' → 
  {y : Y x}{y' : Y x'} → y ≅ y' → 
  {z : Z x y}{z' : Z x' y'} → z ≅ z' →
  {a : A x y z}{a' : A x' y' z'} → a ≅ a' → 
  {b : B x y z a}{b' : B x' y' z' a'} → b ≅ b' → 
  f x y z a b ≅ f x' y' z' a' b'
cong5' f refl refl refl refl refl = refl


subst'-removable : ∀{X}{y z : X} (P : X → Set) (p : y ≅ z) (x : P y) → subst' P p x ≅ x
subst'-removable P refl x = refl

≡-to-≅ : ∀{X}{x y : X} → x ≡ y → x ≅ y
≡-to-≅ refl = refl

-- pairs
record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field fst : A
        snd : B fst

open Σ public

_×_ : Set → Set → Set
A × B = Σ A λ _ → B