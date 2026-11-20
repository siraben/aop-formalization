{-# OPTIONS --safe --without-K #-}
module AoP.LexicalPairs where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import AoP.LexicalOrder using (_then_)
open import AoP.Relations using (_←_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §4.4 worked example. Compare pairs of naturals first by their first
-- coordinate, consulting the second only on a tie. Thus (1,9) precedes
-- (2,0), while comparing (2,1) to (2,3) uses the second coordinate.
Pair = Nat × Nat
first second : Pair ← Pair
first p q = fst p ≤ fst q
second p q = snd p ≤ snd q
lex = first then second

Cases : Pair ← Pair
Cases (a , b) (c , d) = (suc a ≤ c) ⊎ ((a ≡ c) × (b ≤ d))

private
  classify : ∀ {a c} → a ≤ c → (suc a ≤ c) ⊎ (a ≡ c)
  classify {c = zero} z≤ = inr refl
  classify {c = suc c} z≤ = inl (s≤ z≤)
  classify (s≤ p) with classify p
  ... | inl lt = inl (s≤ lt)
  ... | inr refl = inr refl

  strict : ∀ {a c} → suc a ≤ c → c ≤ a → ∀ {X : Set} → X
  strict {zero} (s≤ _) ()
  strict {suc a} (s≤ p) (s≤ q) = strict p q

split : ∀ {p q} → lex p q → Cases p q
split {a , b} {c , d} (le , k) with classify le
... | inl lt = inl lt
... | inr refl = inr (refl , k (rid a))

combine : ∀ {p q} → Cases p q → lex p q
combine {a , b} {c , d} (inl (s≤ lt)) = weaken lt , (λ reverse → strict (s≤ lt) reverse)
combine {a , b} {.a , d} (inr (refl , le)) = rid a , λ _ → le

first-wins : lex (1 , 9) (2 , 0)
first-wins = combine {1 , 9} {2 , 0} (inl (rid 2))
tied : lex (2 , 1) (2 , 3)
tied = combine {2 , 1} {2 , 3} (inr (refl , s≤ z≤))
