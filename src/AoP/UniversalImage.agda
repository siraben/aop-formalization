{-# OPTIONS --safe --without-K #-}
module AoP.UniversalImage where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
private variable A B C : Set

-- Exercise 2.13. The ordinary image requires one qualifying preimage.
-- The universal image requires *every* preimage to qualify. In particular,
-- an output with no preimages passes the universal test vacuously.
All : (A → B) → (A → Set) → B → Set
All f X b = ∀ a → f a ≡ b → X a

Some : (A → B) → (A → Set) → B → Set
Some f X b = Σ _ λ a → (f a ≡ b) × X a

-- Equality of subsets is mutual inclusion, here checked at each output.
identity-out : (X : A → Set) (a : A) → All (λ x → x) X a → X a
identity-out X a all = all a refl
identity-in : (X : A → Set) (a : A) → X a → All (λ x → x) X a
identity-in X a ok .a refl = ok

compose-out : ∀ (f : A → B) (g : B → C) X c → All (λ a → g (f a)) X c → All g (All f X) c
compose-out f g X c all b gb a fa = all a (cong g fa ∙ gb)
compose-in : ∀ (f : A → B) (g : B → C) X c → All g (All f X) c → All (λ a → g (f a)) X c
compose-in f g X c nested a ga = nested (f a) ga a refl

-- The function that always returns false separates the two actions.
miss : ⊤ → Bool
miss _ = false
vacuous : All miss (λ _ → ⊤) true
vacuous _ ()
absent : Some miss (λ _ → ⊤) true → ⊥
absent (_ , () , _)
