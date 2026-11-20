{-# OPTIONS --safe --without-K #-}
module AoP.NonemptyFolds where

open import AoP.Prelude
open import AoP.Paragraph using (Nonempty; _∷⁺_)
private variable A B : Set

-- §1.3. A nonempty list has a singleton case in place of the empty
-- case. For the head-and-tail representation used by the line breaker,
-- the last element receives the singleton handler; each earlier element
-- receives the cons handler. No default element is required.
fold⁺ : (A → B) → (A → B → B) → Nonempty A → B
fold⁺ {A} {B} single step (a ∷⁺ xs) = go a xs
  where
  go : A → List A → B
  go a [] = single a
  go a (b ∷ bs) = step a (go b bs)

foldr1 : (A → A → A) → Nonempty A → A
foldr1 = fold⁺ (λ a → a)

head : Nonempty A → A
head = foldr1 (λ x _ → x)

first-law : ∀ (a : A) xs → head (a ∷⁺ xs) ≡ a
first-law a [] = refl
first-law a (b ∷ bs) = refl

-- foldr1 must return the input element on a singleton; the general fold
-- can, for example, classify a singleton by returning false regardless
-- of its value. No choice of binary step can achieve that with foldr1.
open import Agda.Builtin.Bool using (Bool; false; true)
open import AoP.Complement using (⊥)
singleton-limit : (step : Bool → Bool → Bool) → foldr1 step (true ∷⁺ []) ≡ false → ⊥
singleton-limit step ()
