{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.FloorRule where

open import AoP.Common.Prelude

-- Exercises 3.18–19. Floors are determined by the integer thresholds
-- they meet. Shift a threshold across division by positive b, then across
-- addition of a: the new threshold b*k-a is again an integer. At that
-- threshold we may replace r by its floor and reverse the calculation.
record _⇔_ (P Q : Set) : Set where
  constructor iff
  field forward : P → Q
        backward : Q → P
open _⇔_

module Ordered {Z : Set} (_≤_ : Z → Z → Set) (reflex : ∀ k → k ≤ k)
               (antisym : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b) where
  indirect : ∀ a b → (a ≡ b) ⇔ (∀ k → (k ≤ a) ⇔ (k ≤ b))
  indirect a b = iff same recover
    where
    same : a ≡ b → ∀ k → (k ≤ a) ⇔ (k ≤ b)
    same refl k = iff (λ p → p) (λ p → p)
    recover : (∀ k → (k ≤ a) ⇔ (k ≤ b)) → a ≡ b
    recover tests = antisym (forward (tests a) (reflex a)) (backward (tests b) (reflex b))

  module Floors {R : Set} (meets : Z → R → Set) (embed : Z → R) (floor : R → Z)
                (integer : ∀ k n → meets k (embed n) ⇔ (k ≤ n))
                (round : ∀ k r → meets k r ⇔ (k ≤ floor r)) where
    -- For the rule of floors take transform(r)=(a+r)/b and pull(k)=b*k-a.
    rule : (transform : R → R) (pull : Z → Z) →
           (∀ k r → meets k (transform r) ⇔ meets (pull k) r) → ∀ r →
           floor (transform r) ≡ floor (transform (embed (floor r)))
    rule f pull shift r = backward (indirect _ _) tests
      where
      chain : ∀ {P Q S} → P ⇔ Q → Q ⇔ S → P ⇔ S
      chain p q = iff (λ x → forward q (forward p x)) (λ x → backward p (backward q x))
      flip : ∀ {P Q} → P ⇔ Q → Q ⇔ P
      flip p = iff (backward p) (forward p)
      tests : ∀ k → (k ≤ floor (f r)) ⇔ (k ≤ floor (f (embed (floor r))))
      tests k = chain (flip (round k (f r))) (chain (shift k r)
                (chain (round (pull k) r) (chain (flip (integer (pull k) (floor r)))
                (chain (flip (shift k (embed (floor r)))) (round k (f (embed (floor r))))))))
