{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanBudget where

import AoP.Chapter04.Complement
open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter07.LongestPrefix
open import AoP.Chapter07.VanTrimming
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. Can the van serve these transactions in at most n blocks?
-- Take the longest secure prefix and spend one block. A refusal on the
-- suffix refutes every competing plan, by the exchange lemma. For a
-- nonempty stream n blocks allow n−1 intermediate visits.
module Greedy (cap : Nat) where
  open Bank cap
  open Prefix {Tx}
  open Trim cap

  absurd-prefix : ∀ {a as} → (a ∷ as) ≼ [] → AoP.Chapter04.Complement.⊥
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
