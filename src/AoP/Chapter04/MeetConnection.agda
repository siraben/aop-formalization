{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.MeetConnection where

open import AoP.Common.Prelude

-- Exercise 4.39. Order pairs componentwise. Duplicating x makes it
-- lie below (a,b) exactly when x is a common lower bound. Thus the
-- diagonal is left adjoint to binary meet. Conversely, the adjunction
-- gives both projections (test it at the meet itself) and pairing.
module Order {P : Set} (_≤_ : P → P → Set) (rid : ∀ x → x ≤ x)
             (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
             (meet : P × P → P) where
  _⊑_ : P × P → P × P → Set
  (a , b) ⊑ (c , d) = (a ≤ c) × (b ≤ d)
  diag : P → P × P
  diag x = x , x
  Connection = ∀ x p → ((diag x ⊑ p) → x ≤ meet p) × ((x ≤ meet p) → diag x ⊑ p)
  Projections = ∀ p → diag (meet p) ⊑ p
  Pairing = ∀ x p → diag x ⊑ p → x ≤ meet p

  connection : Projections → Pairing → Connection
  connection proj pair x p = pair x p , λ h → trans h (fst (proj p)) , trans h (snd (proj p))

  universal : Connection → Projections × Pairing
  universal adj = (λ p → snd (adj (meet p) p) (rid (meet p))) , (λ x p → fst (adj x p))

  diagonal-mono : ∀ {x y} → x ≤ y → diag x ⊑ diag y
  diagonal-mono h = h , h
  meet-mono : Connection → ∀ p q → p ⊑ q → meet p ≤ meet q
  meet-mono adj p q (h , k) with fst (universal adj) p
  ... | left , right = fst (adj (meet p) q) (trans left h , trans right k)
