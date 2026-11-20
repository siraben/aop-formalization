{-# OPTIONS --safe --without-K #-}
module AoP.UnionMinimum where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.WellBounded using (Bounded)

-- Exercise 7.29. To minimize a union, replace each inhabited member
-- set by its minima. Empty sets contribute nothing to either union.
module Law {I A : Set} (R : A ← A) (wb : Bounded R)
           (trans : ∀ {a b c} → R a b → R b c → R a c)
           (family : I → A → Set) where
  Whole Winners : A → Set
  Whole a = Σ I λ i → family i a
  Winners a = Σ I λ i → Min R a (family i)

  reduce : ∀ {a} → Min R a Whole → Min R a Winners
  reduce ((i , member) , best) = (i , member , (λ b x → best b (i , x))) ,
    λ { b (j , x , _) → best b (j , x) }

  restore : ∀ {a} → Min R a Winners → Min R a Whole
  restore ((i , member , _) , best) = (i , member) , lower
    where
    lower : ∀ b → Whole b → R _ b
    lower b (j , x) with wb (family j) b x
    ... | c , m , bound = trans (best c (j , m , bound)) (bound b x)
