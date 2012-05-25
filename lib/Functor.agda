{-# OPTIONS --type-in-type #-}
module lib.Functor where

open import lib.Utils
open import lib.Category

record Fun (C D : Cat) : Set where
  field OMap : Obj C → Obj D
        HMap : {A B : Obj C} → Hom C A B → Hom D (OMap A) (OMap B)
        fid : ∀{A} → HMap (iden C {A}) ≡ iden D {OMap A}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (comp C f g) ≡ comp D (HMap f) (HMap g)

open Fun public

-- example

data List (X : Set) : Set where
  [] : List X
  _::_ : X → List X → List X

lmap : ∀{X Y} → (X → Y) → List X → List Y
lmap f [] = []
lmap f (x :: xs) = f x :: lmap f xs

lmapid : ∀{X}(xs : List X) → lmap id xs ≡ xs
lmapid []        = refl
lmapid (x :: xs) = cong (_::_ x) (lmapid xs)

lmapcomp : ∀{X Y Z}{f : Y → Z}{g : X → Y}(xs : List X) → 
           lmap (f ∘ g) xs ≡ lmap f (lmap g xs)
lmapcomp []        = refl
lmapcomp (x :: xs) = cong (_::_ _) (lmapcomp xs)

ListF : Fun Sets Sets
ListF = record { 
  OMap  = List; 
  HMap  = lmap; 
  fid   = ext lmapid; 
  fcomp = ext lmapcomp}