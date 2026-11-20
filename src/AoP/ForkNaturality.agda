{-# OPTIONS --safe --without-K #-}
module AoP.ForkNaturality where

open import AoP.Prelude
open import AoP.IdentityAlgebra using (Identity)
open import AoP.SquareProductFunctors using (square)
open import AoP.Transformations using (Natural)
open import AoP.Functors using (Functor)
open import Agda.Builtin.Nat using (Nat; suc)

-- §2.3. The component at A duplicates one A. Naturality says that
-- duplicating before changing labels or afterwards gives the same pair.
fork : Natural Identity square
Natural.η fork A x = x , x
Natural.square fork f x = refl

trace : Functor.F₁ square suc (Natural.η fork Nat 2) ≡ (3 , 3)
trace = begin
  Functor.F₁ square suc (Natural.η fork Nat 2)
    ≡⟨ Natural.square fork suc 2 ⟩
  Natural.η fork Nat (suc 2)
    ≡⟨⟩
  (3 , 3) ∎
