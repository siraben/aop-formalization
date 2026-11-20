{-# OPTIONS --safe --without-K #-}
module AoP.Slice where

open import AoP.Prelude
open import AoP.Horner using (tri; map)
open import Agda.Builtin.Nat using (Nat; zero; suc)
private variable A : Set

-- Exercise 3.9. Given rows of possibly different lengths, remove zero
-- entries from the first, one from the next, then two, and so on. A row
-- that runs out simply stays empty. The triangle applies tail once more
-- at each successive row, exactly implementing this indexed specification.
tail : List A → List A
tail [] = []
tail (_ ∷ xs) = xs

drop : Nat → List A → List A
drop zero xs = xs
drop (suc n) xs = tail (drop n xs)

from : Nat → List (List A) → List (List A)
from n [] = []
from n (xs ∷ xss) = drop n xs ∷ from (suc n) xss

advance : ∀ n (xss : List (List A)) → map tail (from n xss) ≡ from (suc n) xss
advance n [] = refl
advance n (xs ∷ xss) = cong (drop (suc n) xs ∷_) (advance (suc n) xss)

slice : List (List A) → List (List A)
slice = tri tail

correct : (rows : List (List A)) → slice rows ≡ from 0 rows
correct [] = refl
correct (xs ∷ rows) = begin
  xs ∷ map tail (slice rows) ≡⟨ cong (λ rs → xs ∷ map tail rs) (correct rows) ⟩
  xs ∷ map tail (from 0 rows) ≡⟨ cong (xs ∷_) (advance 0 rows) ⟩
  from 0 (xs ∷ rows) ∎

example : slice ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ (4 ∷ []) ∷ []) ≡ (1 ∷ []) ∷ (3 ∷ []) ∷ [] ∷ []
example = refl
