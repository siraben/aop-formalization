{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyComparisons where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Rose; Forest; fork; grow; null)
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter07.PartyScoreTable using (module Law)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.44. Instrument the two-score recurrence: charge one
-- call to better (one score comparison) at a fork, none at a sibling
-- join. Each recursive result is computed once. The counter measures
-- comparisons, independent of the representation or size of a score.
module Count {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Law rating z add R rid tr mono cmp
  mutual
    tree : Rose E → (S × S) × Nat
    tree (fork e ts) with forest ts
    ... | (i , o) , n = (o , better (add (rating e) i) o) , suc n
    forest : Forest E → (S × S) × Nat
    forest null = (z , z) , 0
    forest (grow t ts) with tree t | forest ts
    ... | (i , o) , n | (is , os) , m = (add i is , add o os) , (n + m)

  mutual
    employees : Rose E → Nat
    employees (fork e ts) = suc (staff ts)
    staff : Forest E → Nat
    staff null = 0
    staff (grow t ts) = employees t + staff ts

  mutual
    exact : ∀ t → tree t ≡ (scores t , employees t)
    exact (fork e ts) rewrite exactᶠ ts = refl
    exactᶠ : ∀ ts → forest ts ≡ (totals ts , staff ts)
    exactᶠ null = refl
    exactᶠ (grow t ts) rewrite exact t | exactᶠ ts = refl
