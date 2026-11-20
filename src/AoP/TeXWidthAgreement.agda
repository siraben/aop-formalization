{-# OPTIONS --safe --without-K #-}
module AoP.TeXWidthAgreement where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.TeXExternal using (length; Shortest)
import AoP.TeXSinglePrinter as Single
import AoP.TeXBoundedPrinter as Two
open import Agda.Builtin.Nat using (suc)

-- Length is determined by optimality even before tie-breaking is
-- examined. Compare each certificate against the other's actual output.
width : ∀ {n ds es} → Shortest n ds → Shortest n es → length ds ≡ length es
width {ds = ds} {es} a b = anti (Shortest.minimal a es (Shortest.round-trip b)) (Shortest.minimal b ds (Shortest.round-trip a))
  where anti : ∀ {i j} → i ≤ j → j ≤ i → i ≡ j
        anti z≤ z≤ = refl
        anti (s≤ le) (s≤ ge) = cong suc (anti le ge)

agree : ∀ n (b : suc n ≤ 65536) → length (fst (Single.extern n b)) ≡ length (fst (Two.extern n b))
agree n b = width (snd (Single.extern n b)) (snd (Two.extern n b))
