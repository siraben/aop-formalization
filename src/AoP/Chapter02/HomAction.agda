{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.HomAction where

open import AoP.Chapter02.Categories

-- Exercise 2.11. H(A,B) consists of arrows A → B. A map A′ → A
-- changes the source by precomposition, while B → B′ changes the
-- target by postcomposition. Thus H acts on Cᵒᵖ × C and lands in
-- sets of arrows equipped with their given equivalence (hom-setoids).
module Hom {o h e} (C : Category o h e) where
  open Category C
  act : ∀ {A B A′ B′} → Hom A′ A → Hom B B′ → Hom A B → Hom A′ B′
  act u v k = v ∘ (k ∘ u)

  respect : ∀ {A B A′ B′} {u u′ : Hom A′ A} {v v′ : Hom B B′} {k k′ : Hom A B} →
            u ≈ u′ → v ≈ v′ → k ≈ k′ → act u v k ≈ act u′ v′ k′
  respect eu ev ek = compose-cong ev (compose-cong ek eu)

  units : ∀ {A B} (k : Hom A B) → act identity identity k ≈ k
  units k = transitive (unitˡ (k ∘ identity)) (unitʳ k)

  -- Two successive source maps compose in reverse order from the two
  -- target maps. The middle arrow k remains between them throughout.
  comp : ∀ {A B A′ B′ A″ B″} (u : Hom A′ A) (v : Hom B B′)
           (s : Hom A″ A′) (t : Hom B′ B″) (k : Hom A B) →
         act (u ∘ s) (t ∘ v) k ≈ act s t (act u v k)
  comp u v s t k = transitive (assoc t v (k ∘ (u ∘ s)))
    (compose-cong (reflexive {f = t}) inner)
    where
    inner : v ∘ (k ∘ (u ∘ s)) ≈ (v ∘ (k ∘ u)) ∘ s
    inner = transitive (compose-cong (reflexive {f = v}) (symmetric (assoc k u s)))
                       (symmetric (assoc v (k ∘ u) s))
