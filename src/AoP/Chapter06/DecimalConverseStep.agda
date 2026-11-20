{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.DecimalConverseStep where

open import AoP.Common.Prelude
open import AoP.Chapter01.PositiveFold using (Positive; encode)
open import AoP.Chapter01.DecimalDigits using (Digits; first; append; Nonzero; Digit; eval; index; scale)
open import AoP.Chapter04.Relations using (_←_; _⊆_)

-- §6.1. Unroll the converse of decimal valuation before deciding
-- how to divide. A solution either explains a single nonzero digit
-- or supplies a smaller representation and one final digit. At this
-- point the equation itself supplies no terminating search strategy.
Reads : Digits ← Positive
Reads ds n = eval ds ≡ n

data Layer (X : Digits ← Positive) : Digits ← Positive where
  stop : ∀ d → Layer X (first d) (encode (index d))
  more : ∀ {ds q} d → X ds q → Layer X (append ds d) (scale q d)

unroll : Reads ⊆ Layer Reads
unroll {first d} refl = stop d
unroll {append ds d} refl = more d refl
roll : Layer Reads ⊆ Reads
roll (stop d) = refl
roll (more d eq) = cong (λ n → scale n d) eq

-- Structural induction identifies every fixed point with Reads. This
-- induction follows the candidate digit string, not the number; an
-- executable printer must still choose the branch from the number.
module Fixed (X : Digits ← Positive) (out : X ⊆ Layer X) (into : Layer X ⊆ X) where
  sound : ∀ ds {n} → X ds n → Reads ds n
  sound (first d) p with out p
  ... | stop .d = refl
  sound (append ds d) p with out p
  ... | more .d pre = cong (λ n → scale n d) (sound ds pre)
  complete : ∀ ds {n} → Reads ds n → X ds n
  complete (first d) refl = into (stop d)
  complete (append ds d) refl = into (more d (complete ds refl))
