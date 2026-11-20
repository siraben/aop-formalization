{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.LexicalOrder where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.RelImplication using (_⇒_)
private variable A : Set

-- Exercise 4.34. Compare by R first. If the reverse R-edge also
-- exists (a tie), S must accept the pair. A reverse edge across two
-- consecutive comparisons forces a tie in each of them by transitivity.
infixr 5 _then_
_then_ : (A ← A) → (A ← A) → A ← A
R then S = R ⊓ ((R ˘) ⇒ S)

record Pre (R : A ← A) : Set where
  field self : ∀ a → R a a
        step : ∀ {x y z} → R x y → R y z → R x z
open Pre

combine : {R S : A ← A} → Pre R → Pre S → Pre (R then S)
self (combine p q) a = self p a , λ _ → self q a
step (combine p q) (r , k) (s , l) = step p r s , λ t →
  step q (k (step p s t)) (l (step p t r))

module Laws (R S T : A ← A) where
  associate : (R then S) then T ⊆ R then (S then T)
  associate ((r , k) , h) = r , λ rr → k rr , λ ss → h (rr , λ _ → ss)
  unassociate : R then (S then T) ⊆ (R then S) then T
  unassociate (r , k) = (r , (λ rr → fst (k rr))) , λ { (rr , l) → snd (k rr) (l r) }

  all : A ← A
  all _ _ = ⊤
  left : all then R ⊆ R
  left (_ , k) = k tt
  left′ : R ⊆ all then R
  left′ r = tt , λ _ → r
  right : R then all ⊆ R
  right = fst
  right′ : R ⊆ R then all
  right′ r = r , λ _ → tt
