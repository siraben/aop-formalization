{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXSinglePrinter where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; weaken)
open import AoP.Chapter10.TeXResidualLoop using (Result; printed)
open import AoP.Chapter10.TeXLoopWidth using (Short; module Proof)
open import AoP.Chapter10.TeXRoundInterval using (module Decimal)
open import AoP.Chapter10.TeXLoopRoundTrip using (module Positive)
open import AoP.Chapter10.TeXClosestShortest using (numerator)
open import AoP.Chapter10.TeXExternal using (length; Shortest; shortest; zero-shortest)
open import AoP.Chapter03.TeXFraction using (Digit; intern)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

module Certified (t : Nat) (b : suc (suc (suc (t * 2))) ≤ 131072) where
  open Positive t b
  minimal : ∀ ds → result ≡ printed ds → ∀ es → intern es ≡ suc t → length ds ≤ length es
  minimal ds eq es yes = project result eq (Proof.minimal 131071 5 lo j b es (numerator es) (Decimal.into t es yes))
    where project : ∀ r → r ≡ printed ds → Short es r → length ds ≤ length es
          project .(printed ds) refl h = h
  -- Clients can transport the run equation without reducing the five-step run.
  opaque
    solve : Σ (List Digit) (λ ds → (result ≡ printed ds) × Shortest (suc t) ds)
    solve = finish output
      where finish : Σ (List Digit) (λ ds → (result ≡ printed ds) × (intern ds ≡ suc t)) → Σ (List Digit) (λ ds → (result ≡ printed ds) × Shortest (suc t) ds)
            finish (ds , (eq , ok)) = ds , (eq , shortest ok (minimal ds eq))

extern : ∀ n → suc n ≤ 65536 → Σ (List Digit) (Shortest n)
extern 0 _ = [] , zero-shortest
extern (suc t) within = fst solution , snd (snd solution)
  where bound = chain (weaken (rid _)) (Arithmetic.scale 2 {a = suc (suc t)} {b = 65536} within)
        solution = Certified.solve t bound
