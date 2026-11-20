{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.BagCountPermutation where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Perm; Insert; front; later; empty; insert)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 5.28. Represent a finite bag by its multiplicity function.
-- Equality of bags compares counts pointwise, including repeated keys.
module Law {A : Set} (eq : ∀ x y → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  bump : A → A → Nat → Nat
  bump a x n with eq a x
  ... | inl _ = suc n
  ... | inr _ = n
  count : A → List A → Nat
  count a [] = 0
  count a (x ∷ xs) = bump a x (count a xs)
  Same : List A → List A → Set
  Same xs ys = ∀ a → count a xs ≡ count a ys
  private
    commute : ∀ a x y n → bump a x (bump a y n) ≡ bump a y (bump a x n)
    commute a x y n with eq a x | eq a y
    ... | inl _ | inl _ = refl
    ... | inl _ | inr _ = refl
    ... | inr _ | inl _ = refl
    ... | inr _ | inr _ = refl
    cancel : ∀ a x m n → bump a x m ≡ bump a x n → m ≡ n
    cancel a x m n p with eq a x
    ... | inr _ = p
    ... | inl _ = cong pred p where pred : Nat → Nat
                                    pred 0 = 0
                                    pred (suc k) = k
    back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    back refl = refl
    self : ∀ a n → bump a a n ≡ suc n
    self a n with eq a a
    ... | inl _ = refl
    ... | inr no with no refl
    ...   | ()
    absurd : ∀ {X : Set} → ⊥ → X
    absurd ()

  increment : ∀ {x xs ys} → Insert x xs ys → ∀ a → count a ys ≡ bump a x (count a xs)
  increment front a = refl
  increment (later {x = y} i) a = cong (bump a y) (increment i a) ∙ commute a y _ _
  sound : ∀ {xs ys} → Perm xs ys → Same xs ys
  sound empty a = refl
  sound (insert {a = x} p i) a = cong (bump a x) (sound p a) ∙ back (increment i a)

  private
    find : ∀ x ys → (count x ys ≡ 0 → ⊥) → Σ (List A) λ zs → Insert x zs ys
    find x [] nonzero = absurd (nonzero refl)
    find x (y ∷ ys) nonzero with eq x y
    ... | inl refl = ys , front
    ... | inr no with find x ys nonzero
    ...   | zs , i = (y ∷ zs) , later i
    clash : ∀ {n} → suc n ≡ 0 → ⊥
    clash ()

  complete : ∀ xs ys → Same xs ys → Perm xs ys
  complete [] [] same = empty
  complete [] (y ∷ ys) same = absurd (clash (back (same y ∙ self y _)))
  complete (x ∷ xs) ys same with find x ys (λ zero → clash (back (self x _) ∙ same x ∙ zero))
  ... | zs , i = insert (complete xs zs (λ a → cancel a x _ _ (same a ∙ increment i a))) i
