{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.TakeWhileGreedy where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter07.GreedyFold using (module Lists)
open import AoP.Chapter07.TakeWhilePrefix using (module Law)

-- Exercise 7.39 via the greedy theorem. Fold candidates are formed
-- by stopping, or by retaining a passing head. A longer tail can
-- simulate either step of a shorter one, using the very same branch.
module Proof {A : Set} (P : A → Set) (test : ∀ a → P a ⊎ (P a → ⊥)) where
  open Law P test using (take)
  Longer : List A ← List A
  Longer ys zs = len zs ≤ len ys
  data Step : List A ← (A × List A) where
    stop : ∀ {x xs} → Step [] (x , xs)
    keep : ∀ {x xs} → P x → Step (x ∷ xs) (x , xs)

  match : ∀ {x b c z} → Longer b c → Step z (x , c) → Σ _ λ y → Step y (x , b) × Longer y z
  match le stop = [] , stop , z≤
  match le (keep p) = _ , keep p , s≤ le

  module G = Lists Longer (λ p q → chain q p) (λ xs → xs ≡ []) Step match

  greedy : ∀ xs → G.Greedy (take xs) xs
  greedy [] = G.seed (refl , λ { _ refl → z≤ })
  greedy (x ∷ xs) with test x
  ... | inl p = G.step (greedy xs) (keep p , λ { _ stop → z≤ ; _ (keep _) → rid _ })
  ... | inr no = G.step (greedy xs) (stop , λ { _ stop → z≤ ; _ (keep p) → absurd (no p) })
    where absurd : ∀ {X : Set} → ⊥ → X
          absurd ()

  bound : ∀ xs ys → Fold (λ zs → zs ≡ []) Step ys xs → len ys ≤ len (take xs)
  bound xs ys = G.bound (greedy xs)
