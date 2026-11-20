{-# OPTIONS --safe --without-K #-}
module AoP.SetoidImageFactor where

open import AoP.Prelude
open import AoP.Relations

-- Exercise 4.20: present the quotient by the kernel of f as a setoid.
-- Representatives are inputs. Two representatives denote the same image
-- element precisely when their outputs agree. This avoids choosing a
-- canonical preimage or asserting equality of witnesses of membership.
module Image {A B : Set} (f : A → B) where
  I = A
  EqI : I ← I
  EqI i j = f i ≡ f j
  private
    back : ∀ {T : Set} {x y : T} → x ≡ y → y ≡ x
    back refl = refl
  reflexive : ∀ i → EqI i i
  reflexive i = refl
  symmetric : ∀ {i j} → EqI i j → EqI j i
  symmetric = back
  transitive : ∀ {i j k} → EqI i j → EqI j k → EqI i k
  transitive = _∙_

  -- Graphs of the quotient map and the inclusion into B, using the
  -- equality of their respective targets. EqI is identity on the image.
  C : I ← A
  C i a = EqI i a
  M : B ← I
  M b i = b ≡ f i
  F : B ← A
  F b a = b ≡ f a
  factor : F ⊆ M ∘ C
  factor {a = a} eq = a , (eq , refl)
  compose : M ∘ C ⊆ F
  compose (i , (eq , same)) = eq ∙ same
  onto : EqI ⊆ C ∘ C ˘
  onto {a = j} eq = j , (eq , refl)
  onto-back : C ∘ C ˘ ⊆ EqI
  onto-back (a , (p , q)) = p ∙ back q
  monic : M ˘ ∘ M ⊆ EqI
  monic (b , (p , q)) = back p ∙ q
  monic-back : EqI ⊆ M ˘ ∘ M
  monic-back {b = i} eq = f i , (refl , eq)
