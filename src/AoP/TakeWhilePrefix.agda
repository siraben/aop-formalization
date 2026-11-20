{-# OPTIONS --safe --without-K #-}
module AoP.TakeWhilePrefix where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)

-- Exercise 7.39. Feasible prefixes can stop immediately, or keep a
-- passing head and continue in the tail. If the test fails, stopping
-- is the sole branch; if it passes, keeping the head dominates stopping.
module Law {A : Set} (P : A → Set) (test : ∀ x → P x ⊎ (P x → ⊥)) where
  data Feasible : List A → List A → Set where
    stop : ∀ {xs} → Feasible [] xs
    keep : ∀ {x ys xs} → P x → Feasible ys xs → Feasible (x ∷ ys) (x ∷ xs)

  take : List A → List A
  take [] = []
  take (x ∷ xs) with test x
  ... | inl _ = x ∷ take xs
  ... | inr _ = []

  feasible : ∀ xs → Feasible (take xs) xs
  feasible [] = stop
  feasible (x ∷ xs) with test x
  ... | inl p = keep p (feasible xs)
  ... | inr _ = stop

  -- Stronger than the length bound: every feasible prefix is itself
  -- a prefix of the answer. Mutual prefix inclusion forces equality.
  dominates : ∀ {ys xs} → Feasible ys xs → Feasible ys (take xs)
  dominates stop = stop
  dominates (keep {x} p tail) with test x
  ... | inl _ = keep p (dominates tail)
  ... | inr no with no p
  ...   | ()

  strip : ∀ {x y xs ys} → Feasible (x ∷ xs) (y ∷ ys) → Feasible xs ys
  strip (keep _ f) = f

  antisym : ∀ {xs ys} → Feasible xs ys → Feasible ys xs → xs ≡ ys
  antisym stop stop = refl
  antisym (keep p f) g = cong (_ ∷_) (antisym f (strip g))

  unique : ∀ {xs ys} → Feasible ys xs → (∀ zs → Feasible zs xs → Feasible zs ys) → ys ≡ take xs
  unique {xs} f longest = antisym (dominates f) (longest (take xs) (feasible xs))
