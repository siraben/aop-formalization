{-# OPTIONS --safe --without-K #-}
module AoP.Splits where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Horner using (map)
open import AoP.Subsequences using (_∈_; here; there; image; preimage)
private variable A : Set

-- §5.6. A split cuts at one boundary: unlike a subsequence, neither
-- piece skips any element. The empty prefix and empty suffix count too.
-- Thus [a,b] has three cuts, including ([],[a,b]) and ([a,b],[]).
-- Reading concatenation backwards is a specification; `splits` computes
-- the finite list of *all* witnesses to that inverse relation.
shift : A → List A × List A → List A × List A
shift a (l , r) = (a ∷ l) , r

splits : List A → List (List A × List A)
splits [] = ([] , []) ∷ []
splits (a ∷ xs) = ([] , a ∷ xs) ∷ map (shift a) (splits xs)

join : List A × List A → List A
join (l , r) = l ++ r

sound : (xs : List A) {p : List A × List A} → p ∈ splits xs → join p ≡ xs
sound [] here = refl
sound [] (there ())
sound (a ∷ xs) here = refl
sound (a ∷ xs) (there m) with preimage (shift a) (splits xs) m
... | (l , r) , w , refl = begin
  join (shift a (l , r)) ≡⟨⟩
  a ∷ (l ++ r)           ≡⟨ cong (a ∷_) (sound xs w) ⟩
  a ∷ xs ∎

complete : (l r : List A) → (l , r) ∈ splits (l ++ r)
complete [] [] = here
complete [] (_ ∷ _) = here
complete (a ∷ l) r = there (image (shift a) (complete l r))
