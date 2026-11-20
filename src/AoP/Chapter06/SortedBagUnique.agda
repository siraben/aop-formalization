{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SortedBagUnique where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter05.BagCountPermutation using (module Law)
open import AoP.Chapter06.SelectionSort using (Sorted; nil; cons)
open import AoP.Chapter06.Selection using (Lower; below)
open import AoP.Chapter05.Permutations using (Perm; insert; Insert; front; later)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

dec : ∀ (x y : Nat) → (x ≡ y) ⊎ (x ≡ y → ⊥)
dec 0 0 = inl refl
dec 0 (suc y) = inr λ ()
dec (suc x) 0 = inr λ ()
dec (suc x) (suc y) with dec x y
... | inl refl = inl refl
... | inr n = inr λ { refl → n refl }
open Law dec
private
  member-bound : ∀ {a x xs ys} → Insert a xs ys → Lower x ys → x ≤ a
  member-bound front (below h _) = h
  member-bound (later i) (below _ tail) = member-bound i tail
  heads : ∀ {a b xs ys} → Perm (a ∷ xs) (b ∷ ys) → Lower b ys → b ≤ a
  heads (insert _ i) l = member-bound i (below (rid _) l)
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
  anti : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b
  anti z≤ z≤ = refl
  anti (s≤ p) (s≤ q) = cong suc (anti p q)
  tail : ∀ x xs ys → Same (x ∷ xs) (x ∷ ys) → Same xs ys
  tail x xs ys same a = cancel a x (count a xs) (count a ys) (same a)
    where cancel : ∀ a x m n → bump a x m ≡ bump a x n → m ≡ n
          cancel a x m n p with dec a x
          ... | inr _ = p
          ... | inl _ = cong pred p where pred : Nat → Nat
                                          pred 0 = 0
                                          pred (suc k) = k
  empty-case : ∀ {x : Nat} {xs} → Perm (x ∷ xs) [] → ⊥
  empty-case (insert p ())
  absurd : ∀ {A : Set} → ⊥ → A
  absurd ()

-- §6.6. Equal multiplicities force the two least keys to coincide.
-- Cancel exactly one copy before repeating on the sorted tails.
unique : ∀ xs ys → Sorted xs → Sorted ys → Same xs ys → xs ≡ ys
unique [] [] _ _ _ = refl
unique [] (y ∷ ys) _ _ same = absurd (empty-case (complete (y ∷ ys) [] (λ a → sym (same a))))
unique (x ∷ xs) [] _ _ same = absurd (empty-case (complete (x ∷ xs) [] same))
unique (x ∷ xs) (y ∷ ys) (cons l sx) (cons r sy) same with anti (heads (complete (y ∷ ys) (x ∷ xs) (λ a → sym (same a))) l) (heads (complete (x ∷ xs) (y ∷ ys) same) r)
... | refl = cong (x ∷_) (unique xs ys sx sy (tail x xs ys same))
