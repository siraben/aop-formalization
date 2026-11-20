{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.SecureSubsequence where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Common.NatOrder using (z≤; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Relations using (Fold; nil; cons)
open import AoP.Chapter05.Refinement using (Choice; keep; skip)

-- Exercise 7.50. With capacity one the alternating stream can be
-- served without a visit. Delete its withdrawal and the two deposits
-- overflow even from the smallest possible initial reserve.
open Bank 1
stream = deposit 1 ∷ withdraw 1 ∷ deposit 1 ∷ []
selected = deposit 1 ∷ deposit 1 ∷ []

works : Secure stream
works = 0 , 1 , post z≤ (credit 1 0) (post (s≤ z≤) (debit 1 0) (post z≤ (credit 1 0) (stop (s≤ z≤))))

subsequence : Fold (λ xs → xs ≡ []) Choice selected stream
subsequence = cons keep (cons skip (cons keep (nil refl)))

overflow : Secure selected → ⊥
overflow (_ , _ , post _ (credit .1 _) (post _ (credit .1 _) (stop (s≤ ()))))
