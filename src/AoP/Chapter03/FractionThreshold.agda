{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.FractionThreshold where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; chain; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 3.19. Write a nonnegative rational in mixed form n+r/d
-- with r<d. After adding a and dividing by b>0, integer threshold k
-- is met iff (b*k)*d ≤ (a+n)*d+r. The remainder cannot affect this
-- comparison: it occupies less than one whole denominator block.
private
  pad : ∀ x r → x ≤ x + r
  pad 0 r = z≤
  pad (suc x) r = s≤ (pad x r)
  cancel : ∀ x {u v} → x + u ≤ x + v → u ≤ v
  cancel 0 p = p
  cancel (suc x) (s≤ p) = cancel x p
  assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  assoc 0 y z = refl
  assoc (suc x) y z = cong suc (assoc x y z)
  impossible : ∀ {k} {X : Set} → suc k ≤ k → X
  impossible {0} ()
  impossible {suc k} (s≤ p) = impossible p

strip : ∀ t n d r → suc r ≤ d → t * d ≤ n * d + r → t ≤ n
strip 0 n d r small le = z≤
strip (suc t) 0 d r small le = impossible (chain small (chain (pad d (t * d)) le))
strip (suc t) (suc n) d r small le rewrite assoc d (n * d) r = s≤ (strip t n d r small (cancel d le))

insert : ∀ t n d r → t ≤ n → t * d ≤ n * d + r
insert 0 n d r le = z≤
insert (suc t) (suc n) d r (s≤ le) rewrite assoc d (n * d) r = sum-mono (rid d) (insert t n d r le)

threshold : ∀ a b k n d r → suc r ≤ d →
  (((b * k) * d ≤ (a + n) * d + r) → b * k ≤ a + n) ×
  ((b * k ≤ a + n) → (b * k) * d ≤ (a + n) * d + r)
threshold a b k n d r small = strip (b * k) (a + n) d r small , insert (b * k) (a + n) d r
