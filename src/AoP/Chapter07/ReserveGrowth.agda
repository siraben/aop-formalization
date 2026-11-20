{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ReserveGrowth where

open import AoP.Common.Prelude
open import AoP.Chapter07.ReserveClipping using (stock; space)
open import AoP.Chapter07.SignedSegment using (down; up; repeat; _≤_; pp; nn; np; up-mono; down-mono; repeat-mono)
open import AoP.Common.NatOrder using (z≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Int using (Int; pos; negsuc)

-- Because the empty prefix has sum zero, the floor is nonpositive
-- and the ceiling nonnegative. On these sides, moving away from zero
-- increases the corresponding natural requirement by the full amount.
private
  below : ∀ {x} → x ≤ pos 0 → down x ≤ pos 0
  below (pp z≤) = np
  below np = np
  above : ∀ {x} → pos 0 ≤ x → pos 0 ≤ up x
  above (pp p) = pp z≤
  debit : ∀ x → x ≤ pos 0 → stock (down x) ≡ suc (stock x)
  debit (pos _) (pp z≤) = refl
  debit (negsuc _) _ = refl
  credit : ∀ x → pos 0 ≤ x → space (up x) ≡ suc (space x)
  credit (pos _) _ = refl
  debit-side : ∀ k x → x ≤ pos 0 → repeat k down x ≤ pos 0
  debit-side 0 x h = h
  debit-side (suc k) x h = below (debit-side k x h)
  credit-side : ∀ k x → pos 0 ≤ x → pos 0 ≤ repeat k up x
  credit-side 0 x h = h
  credit-side (suc k) x h = above (credit-side k x h)

require-stock : ∀ n x → x ≤ pos 0 → stock (repeat n down x) ≡ n + stock x
require-stock 0 x h = refl
require-stock (suc n) x h = debit (repeat n down x) (debit-side n x h) ∙ cong suc (require-stock n x h)
require-space : ∀ n x → pos 0 ≤ x → space (repeat n up x) ≡ n + space x
require-space 0 x h = refl
require-space (suc n) x h = credit (repeat n up x) (credit-side n x h) ∙ cong suc (require-space n x h)
