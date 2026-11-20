{-# OPTIONS --safe --without-K #-}
module AoP.LastBound where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open Job using (duration)
open import AoP.TardinessBound using (module Limit)
open import AoP.ScheduleDuration using (total)
open import AoP.Subsequences using (_∈_; here; there)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §10.3. Given *any* feasible nonempty schedule, exhibit an actual job
-- that satisfies the penalty bound when completed at the common finish
-- time. The witness is its last occurrence. This existential fact is
-- what lets a minimum over last-job penalties inherit the same bound.
module Witness (k : Nat) where
  open Limit k

  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc zero b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)

  unit : ∀ a → a ≡ a + 0
  unit zero = refl
  unit (suc a) = cong suc (unit a)

  finish-total : ∀ s js → finish s js ≡ s + total js
  finish-total s [] = unit s
  finish-total s (j ∷ js) = begin
    finish (s + duration j) js ≡⟨ finish-total (s + duration j) js ⟩
    (s + duration j) + total js ≡⟨ assoc s (duration j) (total js) ⟩
    s + total (j ∷ js) ∎

  final-job : ∀ {s} j js → Fits s (j ∷ js) →
              Σ Job λ z → (z ∈ (j ∷ js)) × Allowed z (finish s (j ∷ js))
  final-job j [] (step ok empty) = j , here , ok
  final-job j (h ∷ t) (step ok tail) with final-job h t tail
  ... | z , m , admissible = z , there m , admissible
