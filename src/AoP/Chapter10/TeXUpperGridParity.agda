{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXUpperGridParity where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; comm; sym)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- §10.4, exercise 10.14. On the first five decimal grids the upper
-- boundary of a TeX rounding cell never lands on a grid point. Strip
-- the common power of two: the left side is odd, the right side even.
data Even : Nat → Set where
  ez : Even 0
  es : ∀ {n} → Even n → Even (suc (suc n))
data Odd : Nat → Set where
  oz : Odd 1
  os : ∀ {n} → Odd n → Odd (suc (suc n))

private
  disjoint : ∀ {n} → Odd n → Even n → ⊥
  disjoint oz ()
  disjoint (os x) (es y) = disjoint x y
  twice : ∀ n → Even (n * 2)
  twice 0 = ez
  twice (suc n) = es (twice n)
  odd-succ : ∀ {n} → Even n → Odd (suc n)
  odd-succ ez = oz
  odd-succ (es e) = os (odd-succ e)
  add-oe : ∀ {a b} → Odd a → Even b → Odd (a + b)
  add-oe oz e = odd-succ e
  add-oe (os o) e = os (add-oe o e)
  add-oo : ∀ {a b} → Odd a → Odd b → Even (a + b)
  add-oo oz oz = es ez
  add-oo oz (os o) = es (add-oo oz o)
  add-oo (os o) p = es (add-oo o p)
  product-oo : ∀ {a b} → Odd a → Odd b → Odd (a * b)
  product-oo {b = b} oz p rewrite Arithmetic.unit b = p
  product-oo (os o) p = add-oe p (add-oo p (product-oo o p))
  assoc* : ∀ a b c → (a * b) * c ≡ a * (b * c)
  assoc* 0 b c = refl
  assoc* (suc a) b c = dist b (a * b) c ∙ cong (b * c +_) (assoc* a b c)
  cancel+ : ∀ k {a b} → k + a ≡ k + b → a ≡ b
  cancel+ 0 eq = eq
  cancel+ (suc k) eq = cancel+ k (inj eq)
    where inj : ∀ {x y} → suc x ≡ suc y → x ≡ y
          inj refl = refl
  cancel* : ∀ a b k → a * suc k ≡ b * suc k → a ≡ b
  cancel* 0 0 k eq = refl
  cancel* 0 (suc b) k ()
  cancel* (suc a) 0 k ()
  cancel* (suc a) (suc b) k eq = cong suc (cancel* a b k (cancel+ (suc k) eq))

-- D = oddFactor * factor, W = (evenHalf * 2) * factor. Factor the
-- alleged grid equality from both sides using commutativity and the
-- common positive multiplier. No bound on n or on the numerator z.
separate : ∀ u v k n z → Odd u → (suc (n * 2) * (u * suc k)) ≡ (z * ((v * 2) * suc k)) → ⊥
separate u v k n z odd eq with cancel* (suc (n * 2) * u) (z * (v * 2)) k
  (assoc* (suc (n * 2)) u (suc k) ∙ eq ∙ sym (assoc* z (v * 2) (suc k)))
... | e = disjoint (product-oo (odd-succ (twice n)) odd) (transport (e ∙ sym (assoc* z v 2)) (twice (z * v)))
  where transport : ∀ {a b} → a ≡ b → Even b → Even a
        transport refl p = p

-- The five-place termination bound limits executed digit steps to
-- precisely these possible new widths. The odd part of 10^k is 5^k.
data Grid : Nat → Set where
  g1 : Grid 10
  g2 : Grid 100
  g3 : Grid 1000
  g4 : Grid 10000
  g5 : Grid 100000

private
  five : Odd 5
  five = os (os oz)
  p2 : Odd 25
  p2 = product-oo five five
  p3 : Odd 125
  p3 = product-oo five p2
  p4 : Odd 625
  p4 = product-oo five p3

upper-misses : ∀ {D} → Grid D → ∀ n z → suc (n * 2) * D ≡ z * 131072 → ⊥
upper-misses g1 n z = separate 5    32768 1  n z five
upper-misses g2 n z = separate 25   16384 3  n z p2
upper-misses g3 n z = separate 125  8192  7  n z p3
upper-misses g4 n z = separate 625  4096  15 n z p4
upper-misses g5 n z = separate 3125 2048  31 n z (product-oo five p4)
