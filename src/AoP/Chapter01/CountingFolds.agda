{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.CountingFolds where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
private variable A B : Set

-- Exercise 1.11. Fold into a function awaiting the initial accumulator.
-- Each layer updates the accumulator before passing it to the tail.
iterate : (B → A → B) → B → List A → B
iterate h b [] = b
iterate h b (x ∷ xs) = iterate h (h b x) xs

left : (B → A → B) → List A → B → B
left h = ⦅ (λ b → b) ∣ (λ x k b → k (h b x)) ⦆

left-law : ∀ (h : B → A → B) xs b → left h xs b ≡ iterate h b xs
left-law h [] b = refl
left-law h (x ∷ xs) b = left-law h xs (h b x)

-- Exercise 1.12. Fold a list into a function of the requested count.
-- At zero, take stops; drop must return the entire remaining list.
-- Calling the tail's drop function at zero reconstructs that tail.
take-step drop-step : A → (Nat → List A) → Nat → List A
take-step x k zero = []
take-step x k (suc n) = x ∷ k n
drop-step x k zero = x ∷ k zero
drop-step x k (suc n) = k n

take drop : List A → Nat → List A
take = ⦅ (λ _ → []) ∣ take-step ⦆
drop = ⦅ (λ _ → []) ∣ drop-step ⦆

zero-drop : (xs : List A) → drop xs zero ≡ xs
zero-drop [] = refl
zero-drop (x ∷ xs) = cong (x ∷_) (zero-drop xs)

reassemble : ∀ (xs : List A) n → take xs n ++ drop xs n ≡ xs
reassemble [] n = refl
reassemble (x ∷ xs) zero = cong (x ∷_) (zero-drop xs)
reassemble (x ∷ xs) (suc n) = cong (x ∷_) (reassemble xs n)
