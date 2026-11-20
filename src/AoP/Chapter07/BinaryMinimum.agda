{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.BinaryMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)

-- §7.1, implementing min. Given the first element and the remaining
-- list, return a minimum. Select the head on a tie, as in the book's
-- guarded binary minimum. A negative test needs connectedness to
-- establish that retaining the recursive result is sound.
module Select {A : Set} (R : A ← A) (rr : ∀ a → R a a)
              (tr : ∀ {a b c} → R a b → R b c → R a c)
              (test : ∀ a b → R a b ⊎ (R a b → ⊥))
              (total : ∀ a b → R a b ⊎ R b a) where
  private
    absurd : ∀ {X : Set} → ⊥ → X
    absurd ()
    reverse : ∀ a b → (R a b → ⊥) → R b a
    reverse a b no with total a b
    ... | inl yes = absurd (no yes)
    ... | inr ba = ba

  open import AoP.Chapter05.Subsequences using (_∈_; here; there)
  open import AoP.Chapter08.Thinning using (Min)
  spec : ∀ a xs → Set
  spec a xs = Σ A λ m → Min R m (λ x → x ∈ (a ∷ xs))

  solve : ∀ a xs → spec a xs
  solve a [] = a , here , λ { _ here → rr a ; _ (there ()) }
  solve a (b ∷ bs) with solve b bs
  ... | m , member , bound with test a m
  ...   | inl am = a , here , λ { _ here → rr a ; x (there p) → tr am (bound x p) }
  ...   | inr no = m , there member , λ { _ here → reverse a m no ; x (there p) → bound x p }
