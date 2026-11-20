{-# OPTIONS --safe --without-K #-}
module AoP.ZippedSplits where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Inverses using (zip)
open import AoP.Splits using (shift; splits)
private variable A : Set

-- §5.6. Pair prefixes from shortest to longest with suffixes from
-- longest to shortest: each pair then uses the same cut position.
-- Prove equality of the enumerations, preserving their order as well
-- as their members. This transfers the soundness and completeness of
-- the direct splits recurrence to the book's zipped construction.
inits : List A → List (List A)
inits [] = [] ∷ []
inits (x ∷ xs) = [] ∷ map (x ∷_) (inits xs)

tails : List A → List (List A)
tails [] = [] ∷ []
tails (x ∷ xs) = (x ∷ xs) ∷ tails xs

push : (x : A) (ls rs : List (List A)) → zip (map (x ∷_) ls) rs ≡ map (shift x) (zip ls rs)
push x [] rs = refl
push x (l ∷ ls) [] = refl
push x (l ∷ ls) (r ∷ rs) = cong (((x ∷ l) , r) ∷_) (push x ls rs)

correct : (xs : List A) → zip (inits xs) (tails xs) ≡ splits xs
correct [] = refl
correct (x ∷ xs) = cong (([] , x ∷ xs) ∷_) (begin
  zip (map (x ∷_) (inits xs)) (tails xs) ≡⟨ push x (inits xs) (tails xs) ⟩
  map (shift x) (zip (inits xs) (tails xs)) ≡⟨ cong (map (shift x)) (correct xs) ⟩
  map (shift x) (splits xs) ∎)
