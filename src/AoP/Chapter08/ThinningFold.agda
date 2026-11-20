{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ThinningFold where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning

-- §8.1: the list instance of the thinning theorem. Imagine a search
-- that generates several partial routes after each input symbol. Keeping
-- only dominating representatives is safe if *every* continuation from
-- a discarded route can be matched from its representative. Compare
-- GreedyFold: here the intermediate set need not have a single minimum.
module Lists {A B : Set} (Q : B ← B)
             (trans : ∀ {a b c} → Q a b → Q b c → Q a c)
             (E : Pred B) (F : B ← (A × B))
             (match : ∀ {x a b c} → Q a b → F c (x , b) →
                      Σ B λ d → F d (x , a) × Q d c) where
  Next : A → Pred B → Pred B
  Next x X c = Σ B λ b → X b × F c (x , b)

  -- An implementation chooses a candidate set for each suffix. It must
  -- thin the base and each one-step expansion. The rest follows by
  -- induction; this separates the algorithm's local and global duties.
  module Run (table : List A → Pred B) (base : Thin Q (table []) E)
             (prune : ∀ x xs → Thin Q (table (x ∷ xs)) (Next x (table xs))) where
    exact : List A → Pred B
    exact xs c = Fold E F c xs

    expand : ∀ x xs → Thin Q (table xs) (exact xs) →
             Thin Q (Next x (table xs)) (exact (x ∷ xs))
    Thin.subset (expand x xs t) (b , p , f) = cons f (Thin.subset t p)
    Thin.cover (expand x xs t) _ (cons f tail) with Thin.cover t _ tail
    ... | a , p , ab with match ab f
    ...   | d , g , dc = d , (a , p , g) , dc

    correct : ∀ xs → Thin Q (table xs) (exact xs)
    Thin.subset (correct []) p = nil (Thin.subset base p)
    Thin.cover (correct []) b (nil e) = Thin.cover base b e
    correct (x ∷ xs) = thin-compose trans (prune x xs) (expand x xs (correct xs))
