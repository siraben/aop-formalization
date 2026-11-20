{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.RoundingCollision where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter03.TeXFraction using (Digit; digit; intern)
open import AoP.Common.NatOrder using (z≤; s≤)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 3.22. A single input c distinguishes two states after the
-- update, even though observation f identifies them beforehand. Hence
-- an update on observed values cannot implement the same computation.
collision : ∀ {A B C : Set} (f : B → A) (step : C → B → B) c x y →
            f x ≡ f y → (f (step c x) ≡ f (step c y) → ⊥) →
            (update : C → A → A) → (∀ c b → f (step c b) ≡ update c (f b)) → ⊥
collision f step c x y equal distinct update law = distinct (begin
  f (step c x) ≡⟨ law c x ⟩
  update c (f x) ≡⟨ cong (update c) equal ⟩
  update c (f y) ≡⟨ back (law c y) ⟩
  f (step c y) ∎)
  where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
        back refl = refl

-- Concrete decimal inputs: .00007 and .00008 both round to 5 TeX
-- units. Prepending a zero gives .000007 and .000008, rounding to 0
-- and 1 respectively. Both states arise from actual decimal strings.
z seven eight : Digit
z = digit 0 z≤
seven = digit 7 (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ z≤)))))))
eight = digit 8 (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ z≤))))))))
suffix : Digit → List Digit
suffix d = z ∷ z ∷ z ∷ z ∷ d ∷ []

no-update : (update : Digit → Nat → Nat) → (∀ c ds → intern (c ∷ ds) ≡ update c (intern ds)) → ⊥
no-update = collision intern _∷_ z (suffix seven) (suffix eight) refl (λ ())
