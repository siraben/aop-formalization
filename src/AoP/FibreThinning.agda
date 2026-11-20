{-# OPTIONS --safe --without-K #-}
module AoP.FibreThinning where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Thin; thin; Pred)

-- Exercise 8.6. Thin the candidates generated at one fixed input.
-- Each coverage comparison takes place within that same fibre: the
-- retained candidate is feasible by subset inclusion and the discarded
-- candidate is feasible by hypothesis. Thus comparisons between values
-- with no common input play no role.
module Law {A B : Set} (Q : B ← B) (S : B ← A) (i : A) (X : Pred B) where
  fibre : Pred B
  fibre b = S b i

  Related = Q ⊓ (S ∘ S ˘)

  restrict : Thin Q X fibre → Thin Related X fibre
  restrict t = thin (Thin.subset t) cover
    where cover : ∀ b → fibre b → Σ B λ a → X a × Related a b
          cover b feasible with Thin.cover t b feasible
          ... | a , kept , edge = a , kept , edge , i , Thin.subset t kept , feasible

  forget : Thin Related X fibre → Thin Q X fibre
  forget t = thin (Thin.subset t) cover
    where cover : ∀ b → fibre b → Σ B λ a → X a × Q a b
          cover b feasible with Thin.cover t b feasible
          ... | a , kept , edge , common = a , kept , edge
