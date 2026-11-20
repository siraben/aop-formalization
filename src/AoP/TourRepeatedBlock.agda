{-# OPTIONS --safe --without-K #-}
module AoP.TourRepeatedBlock where

open import AoP.Prelude
open import AoP.TourThinProjection using (module Law)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.Naturality using (_++_)
open import AoP.Horner using (map)

-- Exercise 8.25. Reduce an entire nonempty run of equal endpoint keys
-- to one occurrence, even inside the concatenation of the two streams.
module Block {Key City : Set} (eq : ∀ (x y : Key) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  open Law {Tour = Key} (λ k → k) (λ _ → 0) eq using (push; compact)
  private
    same : ∀ k ks → push k (k ∷ ks) ≡ k ∷ ks
    same k ks with eq k k
    ... | inl _ = refl
    ... | inr no with no refl
    ...   | ()
  twice : ∀ k ks → push k (push k ks) ≡ push k ks
  twice k [] = same k []
  twice k (l ∷ ls) with eq k l
  ... | inl refl = same k ls
  ... | inr _ = same k (l ∷ ls)

  reduce : ∀ k (cs : List City) ks → compact (k ∷ (map (λ _ → k) cs ++ ks)) ≡ compact (k ∷ ks)
  reduce k [] ks = refl
  reduce k (_ ∷ cs) ks = cong (push k) (reduce k cs ks) ∙ twice k (compact ks)
  inside : ∀ pre k (cs : List City) ks → compact (pre ++ (k ∷ (map (λ _ → k) cs ++ ks))) ≡ compact (pre ++ (k ∷ ks))
  inside [] k cs ks = reduce k cs ks
  inside (l ∷ pre) k cs ks = cong (push l) (inside pre k cs ks)
