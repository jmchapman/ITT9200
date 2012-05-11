{-# OPTIONS --type-in-type #-}
module lib.Category where

open import lib.Utils

record Cat : Set where
  field Obj  : Set 
        Hom  : Obj → Obj → Set
        iden : {X : Obj} → Hom X X
        comp : ∀{X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl  : ∀{X Y}{f : Hom X Y} → comp iden f ≡ f
        idr  : ∀{X Y}{f : Hom X Y} → comp f iden ≡ f
        ass  : ∀{W X Y Z}
               {f : Hom Y Z}{g : Hom X Y}{h : Hom W X} → 
               comp f (comp g h) ≡ comp (comp f g) h

open Cat

Sets : Cat
Sets = record {
         Obj  = Set;
         Hom  = λ X Y → (X → Y) ;
         iden = id;
         comp = _∘_;
         idl  = refl;
         idr  = refl;
         ass  = refl}

!Hom : (C : Cat)(A B : Obj C) → Set
!Hom C A B = Σ (Hom C A B) λ f → (g : Hom C A B) → f ≡ g

_op : Cat → Cat
C op = record {
  Obj  = Obj C;
  Hom  = λ X Y → Hom C Y X;
  iden = iden C;
  comp = λ f g → comp C g f;
  idl  = idr C;
  idr  = idl C;
  ass  = sym (ass C)}