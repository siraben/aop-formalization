{-# OPTIONS --safe --without-K #-}
module AoP.SixteenDigitsFail where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit; digit; intern)
open import AoP.NatOrder using (rid; z≤; s≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

take : ∀ {A : Set} → Nat → List A → List A
take 0 _ = []
take (suc n) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

-- At the first boundary 1/131072, the seventeenth digit decides
-- whether the half-up tie is reached. Check the actual §3.3 fold.
private
  z = digit 0 z≤
  a = digit 1 (s≤ z≤)
  b = digit 2 (s≤ (s≤ z≤))
  c = digit 3 (s≤ (s≤ (s≤ z≤)))
  d = digit 4 (s≤ (s≤ (s≤ (s≤ z≤))))
  e = digit 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))
  f = digit 6 (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ z≤))))))
  g = digit 7 (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))))
  i = digit 9 (rid 9)
midpoint : List Digit
midpoint = z ∷ z ∷ z ∷ z ∷ z ∷ g ∷ f ∷ b ∷ i ∷ c ∷ i ∷ d ∷ e ∷ c ∷ a ∷ b ∷ e ∷ []
full : intern midpoint ≡ 1
full = refl
short : intern (take 16 midpoint) ≡ 0
short = refl
fails : (∀ ds → intern ds ≡ intern (take 16 ds)) → ⊥
fails law with law midpoint
... | ()
