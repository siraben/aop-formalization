{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourArmExtension where

open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter08.TourKeyLayer using (module Keys)
open import AoP.Chapter08.TourKeyTransition using (module Layer)
open import AoP.Chapter08.TourArmNormal using (module Law′)
open import AoP.Chapter08.TourThinProjection using (module Law)

-- Exercise 8.25. Extend the descending arm at its end and the ascending
-- arm at its beginning. The transition theorem leaves a compaction on
-- the target; freshness and distinctness discharge it via normality.
module Step (City : Set) where
  open Keys City
  Ne : ∀ {A : Set} → A → A → Set
  Ne x y = x ≡ y → ⊥
  module At (eq : ∀ (x y : Key) → (x ≡ y) ⊎ Ne x y) where
    open Law {Tour = Key} (λ k → k) (λ _ → 0) eq using (compact)
    expand : City → List Key → List Key
    expand b xs = compact (map (left b) xs ++ map (right b) xs)
    private
      snoc : ∀ b c xs rest → L b (xs ++ (c ∷ [])) ++ rest ≡ L b xs ++ ((c , b) ∷ rest)
      snoc b c [] rest = refl
      snoc b c (x ∷ xs) rest = cong ((x , b) ∷_) (snoc b c xs rest)
      back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
      back refl = refl
    extend : ∀ b c u us v vs → let xs = u ∷ us; ys = v ∷ vs; rev = xs ++ (c ∷ []); fwd = c ∷ ys in
             Order.Ordered Ne rev → Order.Ordered Ne fwd → (b ∈ rev → ⊥) →
             expand b (L c xs ++ R c ys) ≡ L b rev ++ R b fwd
    extend b c u us v vs distinct₁ distinct₂ fresh =
      Layer.At.transition City eq b c u us v vs ∙
      cong compact (back (snoc b c (u ∷ us) (R b (c ∷ v ∷ vs)))) ∙
      Law′.At.normal City eq b ((u ∷ us) ++ (c ∷ [])) (c ∷ v ∷ vs) distinct₁ distinct₂ fresh
