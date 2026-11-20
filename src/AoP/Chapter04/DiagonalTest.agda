{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.DiagonalTest where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)

-- Exercise 4.11 in Rel. On a diagonal edge the input and output are
-- the same state. Testing before, after, or on both sides of X thus
-- asks for the very same two witnesses: C accepts and X has a loop.
module Laws {A : Set} (C X : A ← A) (core : C ⊆ Id) where
  Normal : A ← A
  Normal b a = (C b a × X b a) × (b ≡ a)

  record Form (R : A ← A) : Set where
    constructor form
    field normalize : R ⊆ Normal
          rebuild : Normal ⊆ R

  after : Form ((C ∘ X) ⊓ Id)
  Form.normalize after ((i , c , x) , refl) with core c
  ... | refl = (c , x) , refl
  Form.rebuild after ((c , x) , refl) = (_ , c , x) , refl

  before : Form ((X ∘ C) ⊓ Id)
  Form.normalize before ((i , x , c) , refl) with core c
  ... | refl = (c , x) , refl
  Form.rebuild before ((c , x) , refl) = (_ , x , c) , refl

  both : Form ((C ∘ X ∘ C) ⊓ Id)
  Form.normalize both ((i , c , j , x , d) , refl) with core c | core d
  ... | refl | refl = (c , x) , refl
  Form.rebuild both ((c , x) , refl) = (_ , c , _ , x , c) , refl

  left : Form (C ∘ (X ⊓ Id))
  Form.normalize left (_ , c , x , refl) with core c
  ... | refl = (c , x) , refl
  Form.rebuild left ((c , x) , refl) = _ , c , x , refl

  right : Form ((X ⊓ Id) ∘ C)
  Form.normalize right (_ , (x , refl) , c) with core c
  ... | refl = (c , x) , refl
  Form.rebuild right ((c , x) , refl) = _ , (x , refl) , c

  convert : ∀ {R S} → Form R → Form S → R ⊆ S
  convert r s edge = Form.rebuild s (Form.normalize r edge)
