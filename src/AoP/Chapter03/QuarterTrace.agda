{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.QuarterTrace where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; digit; cshift; halve; intern)
open import AoP.Common.NatOrder using (s≤; z≤)

-- §3.3. Follow the right fold on .25: first prepend the units digit
-- of the suffix, then the leading digit, then discard the guard bit.
two five : Digit
two = digit 2 (s≤ (s≤ z≤))
five = digit 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))

suffix : cshift five 0 ≡ 65536
suffix = refl
whole : cshift two 65536 ≡ 32768
whole = refl
result : intern (two ∷ five ∷ []) ≡ 16384
result = begin
  intern (two ∷ five ∷ []) ≡⟨⟩
  halve (cshift two (cshift five 0)) ≡⟨ cong (λ s → halve (cshift two s)) suffix ⟩
  halve (cshift two 65536) ≡⟨ cong halve whole ⟩
  halve 32768 ≡⟨⟩
  16384 ∎
