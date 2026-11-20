{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ListMinimumFold where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Relations
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter07.WellBounded using (Bounded)

-- Exercise 7.29. A singleton wins outright. For each further cons,
-- compare its head with a winner of the tail, retaining both choices
-- on a tie. The empty list supplies no winner. The singleton case
-- is the first nonempty state of the fold.
module Law {A : Set} (R : A ← A) (rr : ∀ a → R a a)
           (tr : ∀ {a b c} → R a b → R b c → R a c) (wb : Bounded R) where
  data Win : A ← List A where
    one : ∀ {a} → Win a (a ∷ [])
    head : ∀ {a b xs} → R a b → Win b xs → Win a (a ∷ xs)
    tail : ∀ {a b xs} → R b a → Win b xs → Win b (a ∷ xs)

  Spec : A ← List A
  Spec a xs = Min R a (λ b → b ∈ xs)

  sound : Win ⊆ Spec
  sound one = here , λ { _ here → rr _ ; _ (there ()) }
  sound (head ab w) with sound w
  ... | _ , lower = here , λ { _ here → rr _ ; c (there m) → tr ab (lower c m) }
  sound (tail ba w) with sound w
  ... | m , lower = there m , λ { _ here → ba ; c (there p) → lower c p }

  extend : ∀ x xs → (∀ b → Spec b xs → Win b xs) → ∀ a → Spec a (x ∷ xs) → Win a (x ∷ xs)
  extend x xs ih a (there m , lower) = tail (lower x here) (ih a (m , λ c p → lower c (there p)))
  extend a [] ih .a (here , lower) = one
  extend a (b ∷ xs) ih .a (here , lower) with wb (λ c → c ∈ (b ∷ xs)) b here
  ... | c , m , best = head (lower c (there m)) (ih c (m , best))

  complete : ∀ xs a → Spec a xs → Win a xs
  complete [] a (() , _)
  complete (x ∷ xs) = extend x xs (complete xs)
