{-# OPTIONS --safe --without-K #-}
module AoP.GridDivision where

open import AoP.Prelude
open import AoP.GridTranslation using (Below; translate)
open import AoP.DivisionThreshold using (sound; complete)
open import Agda.Builtin.Nat using (Nat; suc; div-helper; _*_; _+_)

-- Pull a quotient threshold back through division. The alignment law
-- supplies an old grid index for every pulled-back new grid index.
-- In the decimal fold the divisor is ten and the grid width halves:
-- each new threshold pulls back to five old blocks.
module Law (k w v : Nat) (index : Nat → Nat)
           (aligned : ∀ t → (t * v) * suc k ≡ index t * w) where
  quot : Nat → Nat
  quot n = div-helper 0 k n k

  divide : ∀ {x y} → Below w x y → Below v (quot x) (quot y)
  divide {x} {y} h t given = finish (t * v) (pull (aligned t) (start (t * v) given))
    where
    open import AoP.NatOrder using (_≤_; z≤)
    start : ∀ u → u ≤ quot x → u * suc k ≤ x
    start 0 p = z≤
    start (suc u) p = sound k x k (suc u) p
    pull : ∀ {n} → n ≡ index t * w → n ≤ x → n ≤ y
    pull refl = h (index t)
    finish : ∀ u → u * suc k ≤ y → u ≤ quot y
    finish 0 p = z≤
    finish (suc u) p = complete k y k (suc u) p

  digit-step : ∀ m {x y} → Below w x y → Below v (quot (m * w + x)) (quot (m * w + y))
  digit-step m h = divide (translate w m h)
