{-# OPTIONS --safe --without-K #-}
module AoP.FiniteFrontierBudget where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

Dec : Set → Set
Dec P = P ⊎ (P → ⊥)
size : ∀ {A : Set} → List A → Nat
size [] = 0
size (_ ∷ xs) = suc (size xs)

-- A nonempty frontier spends one token from a finite list covering
-- the unfinished vertices. Keep the rest as a budget, even if some
-- of its tokens now represent finished vertices. Duplicates are safe.
module Scan {A : Set} (Q : A → Set) (test : ∀ x → Dec (Q x)) where
  record Hit (xs : List A) : Set where
    field point : A
          active : Q point
          rest : List A
          cost : size xs ≡ suc (size rest)
          keep : ∀ {x} → (Q x → ⊥) → x ∈ xs → x ∈ rest
  scan : ∀ xs → Hit xs ⊎ (∀ {x} → x ∈ xs → Q x → ⊥)
  scan [] = inr λ ()
  scan (x ∷ xs) with test x
  ... | inl q = inl (record { point = x; active = q; rest = xs; cost = refl; keep = keep })
    where keep : ∀ {y} → (Q y → ⊥) → y ∈ (x ∷ xs) → y ∈ xs
          keep no here with no q
          ... | ()
          keep no (there m) = m
  ... | inr no with scan xs
  ...   | inr absent = inr λ { here → no ; (there m) → absent m }
  ...   | inl h = inl (record { point = Hit.point h; active = Hit.active h; rest = x ∷ Hit.rest h; cost = cong suc (Hit.cost h); keep = λ { n here → here ; n (there m) → there (Hit.keep h n m) } })
