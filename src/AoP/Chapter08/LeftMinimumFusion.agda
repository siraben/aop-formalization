{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.LeftMinimumFusion where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter08.LeftMinimumCount using (module Law)

-- Exercise 8.15. The first element represents its whole block.
-- Extending a block emits nothing; splitting emits the old head
-- and starts tracking the new one. Fuse those equations into the
-- greedy scan so no partition or cut certificate is constructed.
module Fuse {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
            (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
            (test : ∀ a b → Q a b ⊎ (Q a b → ⊥)) where
  open Law Q rr tr test

  heads : ∀ {h xs n} → Cuts h xs n → List A
  heads {h} done = h ∷ []
  heads (extend _ tail) = heads tail
  heads {h} (split tail) = h ∷ heads tail

  run : A → List A → List A
  run h [] = h ∷ []
  run h (x ∷ xs) with test h x
  ... | inl _ = run h xs
  ... | inr _ = h ∷ run x xs

  fusion : ∀ h xs → heads (snd (greedy h xs)) ≡ run h xs
  fusion h [] = refl
  fusion h (x ∷ xs) with test h x
  ... | inl _ = fusion h xs
  ... | inr _ = cong (h ∷_) (fusion x xs)

  -- A cons-list fold into functions of the current head gives the
  -- same scan. Applying its result supplies the first pending block.
  open import AoP.Chapter02.Folds using (⦅_∣_⦆)
  step : A → (A → List A) → A → List A
  step x k h with test h x
  ... | inl _ = k h
  ... | inr _ = h ∷ k x

  folded : List A → A → List A
  folded = ⦅ (λ h → h ∷ []) ∣ step ⦆

  calculate : ∀ xs h → folded xs h ≡ run h xs
  calculate [] h = refl
  calculate (x ∷ xs) h with test h x
  ... | inl _ = calculate xs h
  ... | inr _ = cong (h ∷_) (calculate xs x)
