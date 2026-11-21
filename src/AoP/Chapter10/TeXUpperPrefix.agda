{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXUpperPrefix where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; switch; assoc; sym)
open import AoP.Chapter10.TeXUpperGridParity using (Grid; upper-misses)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; suc)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter10.StrictUpperQuotient using (choose; cell; unique-choice)

-- A prefix of the printed loop, with scale D, prefix numerator z and
-- upper residual q. The only property of the ordinary divmod step we
-- need is quotient-times-divisor plus remainder equals the dividend.
-- Allowing any such split makes the result independent of the lower
-- residual, stop test, and implementation of integer division.
W = 131072
module Prefix (n : Nat) where
  hi = suc (n * 2)
  data Run : Nat → Nat → Nat → Set where
    start : Run 1 0 hi
    emit : ∀ {D z q} d r → Run D z q → d * W + r ≡ q * 10 → Run (D * 10) (z * 10 + d) r

  invariant : ∀ {D z q} → Run D z q → z * W + q ≡ D * hi
  invariant start = sym (Arithmetic.unit hi)
  invariant (emit {D} {z} {q} d r old division) = begin
    (z * 10 + d) * W + r       ≡⟨ cong (_+ r) (dist (z * 10) d W) ⟩
    (z * 10 * W + d * W) + r   ≡⟨ assoc (z * 10 * W) (d * W) r ⟩
    z * 10 * W + (d * W + r)   ≡⟨ cong (z * 10 * W +_) division ⟩
    z * 10 * W + q * 10        ≡⟨ cong (_+ q * 10) (switch z 10 W) ⟩
    z * W * 10 + q * 10        ≡⟨ sym (dist (z * W) q 10) ⟩
    (z * W + q) * 10           ≡⟨ cong (_* 10) (invariant old) ⟩
    D * hi * 10                ≡⟨ switch D hi 10 ⟩
    D * 10 * hi                ∎

  -- An exact quotient would produce a zero residual. The invariant
  -- would then place the upper boundary on the new decimal grid.
  no-zero : ∀ {D z} → Grid D → Run D z 0 → ⊥
  no-zero {D} {z} grid run = upper-misses grid n z (begin
    hi * D         ≡⟨ Arithmetic.comm hi D ⟩
    D * hi         ≡⟨ sym (invariant run) ⟩
    z * W + 0      ≡⟨ Arithmetic.unit (z * W) ⟩
    z * W          ∎)

  inexact : ∀ {D z q} → Grid (D * 10) → Run D z q → ∀ d → d * W ≡ q * 10 → ⊥
  inexact grid old d exact = no-zero grid (emit d 0 old (Arithmetic.unit (d * W) ∙ exact))

  private
    strictify : ∀ a b → a ≤ b → (a ≡ b → ⊥) → suc a ≤ b
    strictify 0 0 le unequal with unequal refl
    ... | ()
    strictify 0 (suc b) le unequal = s≤ z≤
    strictify (suc a) (suc b) (s≤ le) unequal = s≤ (strictify a b le (λ e → unequal (cong suc e)))
    relax : ∀ {a b} → suc a ≤ b → a ≤ b
    relax {0} le = z≤
    relax {suc a} (s≤ le) = s≤ (relax le)

  -- N = 10q = suc m. The ordinary floor d satisfies dW ≤ N < (d+1)W.
  -- Reachability makes the first inequality strict; relaxing the second
  -- gives the defining bounds for the corrected choice floor((N−1)/W).
  same-digit : ∀ {D z q} → Grid (D * 10) → Run D z q → ∀ m → q * 10 ≡ suc m →
               choose 131071 m ≡ choose 131071 (suc m)
  same-digit grid old m positive = unique-choice 131071 m d
    (strictify (d * W) (suc m) (fst ordinary) (λ eq → inexact grid old d (eq ∙ sym positive)) ,
     relax (snd ordinary))
    where d = choose 131071 (suc m)
          ordinary = cell 131071 (suc m)
