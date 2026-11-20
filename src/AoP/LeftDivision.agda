{-# OPTIONS --safe --without-K #-}
module AoP.LeftDivision where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph)
private variable A B C D : Set

-- §4.4. Given R and S with a common target, a left-division edge
-- promises that every R-output at one input is an S-output at the other.
infixr 7 _＼_
_＼_ : (C ← A) → (C ← B) → A ← B
(R ＼ S) a b = ∀ {c} → R c a → S c b

residual : (R : C ← A) (S : C ← B) (X : A ← B) → R ∘ X ⊆ S → X ⊆ R ＼ S
residual R S X law x r = law (_ , r , x)
cancel-left : (R : C ← A) (S : C ← B) (X : A ← B) → X ⊆ R ＼ S → R ∘ X ⊆ S
cancel-left R S X law (_ , r , x) = law x r

-- Exercise 4.35. A graph pins the intermediate input to f d.
-- Consequently it can be moved into the denominator's input or the
-- numerator's input (with a converse on the appropriate side).
module Right (R : C ← A) (S : C ← B) (f : D → B) where
  push : (R ＼ S) ∘ graph f ⊆ R ＼ (S ∘ graph f)
  push (_ , h , refl) r = _ , h r , refl
  pull : R ＼ (S ∘ graph f) ⊆ (R ＼ S) ∘ graph f
  pull {a} {d} h = f d , (λ r → extract (h r)) , refl
    where extract : ∀ {c} → (S ∘ graph f) c d → S c (f d)
          extract (_ , s , refl) = s

module Left (R : C ← A) (S : C ← B) (f : D → A) where
  push : graph f ˘ ∘ (R ＼ S) ⊆ (R ∘ graph f) ＼ S
  push (_ , refl , h) (_ , r , refl) = h r
  pull : (R ∘ graph f) ＼ S ⊆ graph f ˘ ∘ (R ＼ S)
  pull {d} h = f d , refl , λ r → h (f d , r , refl)
