{-# OPTIONS --safe --without-K #-}
module AoP.VanBudget where

import AoP.Complement
open import AoP.Prelude
open import AoP.Reserves
open import AoP.LongestPrefix
open import AoP.VanTrimming
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. Can the van serve these transactions in at most n blocks?
-- Take the longest secure prefix and spend one block. A refusal on the
-- suffix refutes every competing plan, by the exchange lemma. For a
-- nonempty stream n blocks allow n−1 intermediate visits.
module Greedy (cap : Nat) where
  open Bank cap
  open Prefix {Tx}
  open Trim cap

  absurd-prefix : ∀ {a as} → (a ∷ as) ≼ [] → AoP.Complement.⊥
  absurd-prefix ()

  cast : ∀ {n xs ys} → xs ≡ ys → Within n xs → Within n ys
  cast refl p = p

  decide : ∀ n xs → Dec (Within n xs)
  decide n [] = inl done
  decide zero (_ ∷ _) = inr (λ ())
  decide (suc n) (t ∷ ts) with Van.first-block cap (t ∷ ts)
  ... | result [] r eq ok longest = inr λ where
    (block {t = a} {ts = as} {rest = tail} secure plan) →
      absurd-prefix (longest (prefix (a ∷ as) tail) secure)
  ... | g@(result (a ∷ as) r eq ok longest) with decide n r
  ...   | inr no = inr (λ p → no (exchange g p))
  ...   | inl p = inl (cast eq (block ok p))
