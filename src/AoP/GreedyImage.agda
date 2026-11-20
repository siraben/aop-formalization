{-# OPTIONS --safe --without-K #-}
module AoP.GreedyImage where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)

-- Exercise 7.38. Fix a set of competing inputs. First minimize the
-- input, then minimize among the outputs available at that input.
-- For each competing output, converse monotonicity supplies a matching
-- output at the better input. Transitivity finishes the comparison.
module Law {I A : Set} (Q : I ← I) (R : A ← A) (S : A ← I)
           (tr : ∀ {x y z} → R x y → R y z → R x z)
           (match : ∀ {i j z} → Q i j → S z j → Σ A λ y → S y i × R y z) where
  Image : (I → Set) → A → Set
  Image X z = Σ I λ j → S z j × X j

  optimum : ∀ X i z → Min Q i X → Min R z (λ y → S y i) → Min R z (Image X)
  optimum X i z (xi , bestI) (sz , bestZ) = (i , sz , xi) , lower
    where lower : ∀ w → Image X w → R z w
          lower w (j , sw , xj) with match (bestI j xj) sw
          ... | y , sy , yw = tr (bestZ y sy) yw
