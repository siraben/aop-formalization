{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DecimalTriangle where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter03.Horner using (map; tri; module Ruby)
open import AoP.Chapter03.TeXFraction using (Digit)

-- Exercise 3.15. A finite decimal fraction is supplied most-significant
-- digit first. Scale every digit by 1/10, then let the triangle apply
-- one extra scaling per position. Thus .37 denotes 3/10 + 7/100.
-- Horner fusion avoids building the scaled lists. The value carrier is
-- abstract so division here can be exact; integer truncation would not
-- satisfy the distributivity assumption.
module Val {V : Set} (zero : V) (_+_ : V → V → V) (tenth : V → V)
           (value : Digit → V) (empty : zero ≡ tenth zero)
           (dist : ∀ a b → tenth a + tenth b ≡ tenth (a + b)) where
  module H = Ruby zero _+_ tenth empty dist
  first : Digit → V
  first d = tenth (value d)

  expanded : List Digit → V
  expanded ds = H.reduce (tri tenth (map first ds))

  shift : Digit → V → V
  shift d r = tenth (value d + r)

  inline : ∀ ds → ⦅ zero ∣ (λ x r → x + tenth r) ⦆ (map first ds) ≡ ⦅ zero ∣ shift ⦆ ds
  inline [] = refl
  inline (d ∷ ds) = begin
    first d + tenth (⦅ zero ∣ (λ x r → x + tenth r) ⦆ (map first ds))
      ≡⟨ cong (λ r → first d + tenth r) (inline ds) ⟩
    first d + tenth (⦅ zero ∣ shift ⦆ ds) ≡⟨ dist (value d) _ ⟩
    shift d (⦅ zero ∣ shift ⦆ ds) ∎

  correct : ∀ ds → expanded ds ≡ ⦅ zero ∣ shift ⦆ ds
  correct ds = H.horner (map first ds) ∙ inline ds
