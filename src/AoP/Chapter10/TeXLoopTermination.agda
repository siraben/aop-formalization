{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXLoopTermination where

open import AoP.Common.Prelude
open import AoP.Chapter10.TeXResidualLoop
open import AoP.Chapter10.TeXResidualGap using (module Next)
open import AoP.Chapter10.TeXPrinterStep using (module Emit)
open import AoP.Chapter10.TeXFivePlaces using (room)
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken; chain)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

grow : Nat → Nat → Nat
grow 0 g = g
grow (suc n) g = grow n (g * 10)
Success : Result → Set
Success r = Σ (List Digit) (λ ds → r ≡ printed ds)
private
  pad : ∀ p g → g ≤ p + g
  pad 0 g = rid g
  pad (suc p) g = weaken (pad p g)
  absurd : ∀ {g} {X : Set} → suc g ≤ g → X
  absurd {0} ()
  absurd {suc g} (s≤ p) = absurd p
  cast : ∀ {x y z} → y ≡ z → x ≤ y → x ≤ z
  cast refl p = p

module Total (k : Nat) where
  open Loop k
  enough : ∀ fuel p j (bound : suc j ≤ suc k) g → suc k ≤ grow fuel g →
    (∀ r → p ≡ suc r → suc r + g ≤ suc j) → Success (run fuel p j bound)
  enough fuel 0 j bound g room′ gap = [] , refl
  enough 0 (suc p) j bound g room′ gap = absurd (chain (s≤ (pad p g)) (chain (gap p refl) (chain bound room′)))
  enough (suc fuel) (suc p) j bound g room′ gap = lift (enough fuel E.low (pred E.high) (next-bound k E.high E.next-high) (g * 10) room′ next)
    where module E = Emit k j 0 (suc p) bound
          next : ∀ r → E.low ≡ suc r → suc r + g * 10 ≤ suc (pred E.high)
          next r eq = cast (nonzero E.high (fst E.next-high)) (Next.gap k j (suc p) bound g r (gap p refl) eq)
          lift : ∀ {v} → Success v → Success (prepend E.letter v)
          lift (ds , refl) = (E.letter ∷ ds) , refl

five : ∀ p j (b : suc j ≤ 131072) → p + 2 ≤ suc j → Success (Loop.run 131071 5 p j b)
five p j b gap = Total.enough 131071 5 p j b 2 room (λ { _ refl → gap })
