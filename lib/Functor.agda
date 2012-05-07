{-# OPTIONS --type-in-type #-}
module Functor where

open import Utils
open import Category

open Cat

record Fun (C D : Cat) : Set where
  field OMap : Obj C → Obj D
        HMap : {A B : Obj C} → Hom C A B → Hom D (OMap A) (OMap B)
        fid : ∀{A} → HMap (id C {A}) ≡ id D {OMap A}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → HMap (comp C f g) ≡ comp D (HMap f) (HMap g)

data List (X : Set) : Set where
  [] : List X
  _::_ : X → List X → List X

lmap : ∀{X Y} → (X → Y) → List X → List Y
lmap f [] = []
lmap f (x :: xs) = f x :: lmap f xs

ListF : Fun Sets Sets
ListF = record { OMap = List; HMap = lmap; fid = {!!}; fcomp = {!!} }