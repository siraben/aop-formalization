{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.GreedySingleton where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning
import AoP.Chapter08.ThinningFold as T
import AoP.Chapter08.SingletonThinning as S

-- Exercise 8.8 for cons-list programs with a chosen local winner.
-- Store only the winner at each suffix. Local minimality supplies
-- the singleton thinning premises, so the thinning theorem proves
-- the final singleton covers every complete run.
module Law {A B : Set} (Q : B ← B) (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
           (E : Pred B) (F : B ← (A × B))
           (match : ∀ {x a b c} → Q a b → F c (x , b) → Σ B λ d → F d (x , a) × Q d c)
           (win : List A → B) (seed : Min Q (win []) E)
           (step : ∀ x xs → Min Q (win (x ∷ xs)) (λ d → F d (x , win xs))) where
  module L = T.Lists Q tr E F match
  table : List A → Pred B
  table xs d = d ≡ win xs

  prune : ∀ x xs → Thin Q (table (x ∷ xs)) (L.Next x (table xs))
  prune x xs = S.Law.eliminate Q _ _ ((_ , refl , fst (step x xs)) , lower)
    where lower : ∀ d → L.Next x (table xs) d → Q (win (x ∷ xs)) d
          lower d (_ , refl , f) = snd (step x xs) d f

  module Run = L.Run table (S.Law.eliminate Q E _ seed) prune
  optimum : ∀ xs → Min Q (win xs) (λ d → Fold E F d xs)
  optimum xs = S.Law.minimum Q _ _ (Run.correct xs)
