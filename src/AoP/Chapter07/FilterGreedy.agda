{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.FilterGreedy where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; s≤; rid; chain; weaken)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter07.GreedyFold using (module Lists)

-- Exercise 7.41. Drop or retain a passing element; a failing one
-- must be dropped. Unlike takeWhile, dropping the head preserves
-- the tail result. Keeping a passing element always gains one cell.
module Law {A : Set} (P : A → Set) (test : ∀ x → P x ⊎ (P x → ⊥)) where
  data Step : List A ← (A × List A) where
    drop : ∀ {x xs} → Step xs (x , xs)
    keep : ∀ {x xs} → P x → Step (x ∷ xs) (x , xs)
  Longer : List A ← List A
  Longer ys zs = len zs ≤ len ys
  match : ∀ {x b c z} → Longer b c → Step z (x , c) → Σ _ λ y → Step y (x , b) × Longer y z
  match h drop = _ , drop , h
  match h (keep p) = _ , keep p , s≤ h
  module G = Lists Longer (λ p q → chain q p) (λ xs → xs ≡ []) Step match

  filter : List A → List A
  filter [] = []
  filter (x ∷ xs) with test x
  ... | inl _ = x ∷ filter xs
  ... | inr _ = filter xs

  greedy : ∀ xs → G.Greedy (filter xs) xs
  greedy [] = G.seed (refl , λ { _ refl → rid _ })
  greedy (x ∷ xs) with test x
  ... | inl p = G.step (greedy xs) (keep p , λ { _ drop → weaken (rid _) ; _ (keep _) → rid _ })
  ... | inr no = G.step (greedy xs) (drop , λ { _ drop → rid _ ; _ (keep p) → absurd (no p) })
    where absurd : ∀ {X : Set} → ⊥ → X
          absurd ()

  longest : ∀ xs → ∀ {ys} → Fold (λ zs → zs ≡ []) Step ys xs → len ys ≤ len (filter xs)
  longest xs = G.bound (greedy xs)

  -- Equality at the optimum forces every passing head to be kept.
  -- Dropping one would require the tail to beat its own maximum.
  open import Agda.Builtin.Nat using (Nat; zero; suc)
  private
    impossible : ∀ n → suc n ≤ n → ⊥
    impossible zero ()
    impossible (suc n) (s≤ h) = impossible n h

  tight : ∀ {xs ys} → Fold (λ zs → zs ≡ []) Step ys xs → len (filter xs) ≤ len ys → ys ≡ filter xs
  tight (nil refl) h = refl
  tight (cons {x = x} {xs = xs} drop tail) h with test x
  ... | inr _ = tight tail h
  ... | inl _ with impossible (len (filter xs)) (chain h (longest xs tail))
  ...   | ()
  tight (cons {x = x} (keep p) tail) h with test x
  ... | inl _ with h
  ...   | s≤ q = cong (x ∷_) (tight tail q)
  tight (cons {x = x} (keep p) tail) h | inr no with no p
  ... | ()
