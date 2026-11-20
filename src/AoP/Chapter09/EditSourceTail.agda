{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditSourceTail where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditScript
open import AoP.Chapter09.EditTail using (module Law)
open import AoP.Chapter03.Horner using (map)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter01.ConversionCost using (len)
open import Agda.Builtin.Nat using (suc)

module Source {A : Set} where
  open Scripts {A}
  rev-eq : ∀ {B : Set} {x y : B} → x ≡ y → y ≡ x
  rev-eq refl = refl
  flipped-length : ∀ es → len (map flip es) ≡ len es
  flipped-length [] = refl
  flipped-length (_ ∷ es) = cong suc (flipped-length es)
  swapped : ∀ es x y → edit es ≡ (x , y) → edit (map flip es) ≡ (y , x)
  swapped es x y e = begin
    edit (map flip es) ≡⟨ rev-eq (symmetry es) ⟩
    swap (edit es) ≡⟨ cong swap e ⟩
    (y , x) ∎

  -- Swap endpoints, shorten the target, then swap back. Neither swap
  -- changes script length, because each operation has exactly one dual.
  shorten : ∀ es a x y → edit es ≡ (a ∷ x , y) →
            Σ (List (Op A)) λ fs → (edit fs ≡ (x , y)) × (len fs ≤ len es)
  shorten es a x y e with Law.tail-script (map flip es) y a x (swapped es _ _ e)
  ... | fs , eq , le = map flip fs , swapped fs y x eq , bound
    where bound : len (map flip fs) ≤ len es
          bound rewrite flipped-length fs | rev-eq (flipped-length es) = le
