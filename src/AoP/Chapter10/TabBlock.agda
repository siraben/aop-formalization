{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TabBlock where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)
open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter10.Detab
open import AoP.Chapter10.Entab
open import AoP.Chapter10.TabFree
open import AoP.Chapter10.TabDistance
open import AoP.Chapter10.TabEmission
open import AoP.Chapter10.EntabPending
open import AoP.Chapter10.TabCountdown using (module Count)
open import AoP.Chapter01.Snoc using (_▻_)

-- A competing encoding may append one tab. What happens if our encoder
-- reads its entire *expansion*, rather than a tab character? It emits
-- one tab after its committed prefix and clears the buffer, even if some
-- of the blanks before this stop were pending from a previous character.
module Block {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n
  open Image {A} n
  open Emission {A} n
  open Stops {A} n
  open Distance {A} n

  run : Nat → State → State
  run zero s = s
  run (suc k) s = run k (tick s)

  consume : ∀ {s} k (p : Plain s) → view (encode (spaces k p)) ≡ run k (view (encode p))
  consume zero p = refl
  consume (suc k) p = begin
    view (encode (spaces k (space p))) ≡⟨ consume k (space p) ⟩
    run k (view (add-space (encode p))) ≡⟨ cong (run k) (simulates (encode p)) ⟩
    run k (tick (view (encode p))) ∎

  module At (xs : Text) where
    open Prefix xs
    same-run : ∀ k s → run k s ≡ ticks k s
    same-run zero s = refl
    same-run (suc k) s = same-run k (tick s)

    completes : ∀ k → (le : k ≤ m) → run (suc (m - k)) (xs , k) ≡ emit
    completes k le = same-run (suc (m - k)) (xs , k) ∙ trigger (Count.countdown le)

  tab-block : ∀ {s} (p : Plain s) →
    view (encode (spaces (suc (position s)) p)) ≡ (Buffer.code (encode p) ▻ tab , 0)
  tab-block {s} p = consume (suc (position s)) p ∙ finish
    where
    finish : run (suc (position s)) (view (encode p)) ≡ (Buffer.code (encode p) ▻ tab , 0)
    finish with encode p | bounded p | distance p
    ... | buf xs k inv | le | eq = cong (λ j → run (suc j) (xs , k)) eq ∙ At.completes xs k le
