{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ReservePrefixTrace where

open import AoP.Common.Prelude
open import AoP.Chapter07.ReservePrefixGreedy using (sample; module Floor; module Ceiling)
open import AoP.Chapter07.SignedSegment using (module M)
open import Agda.Builtin.Int using (pos; negsuc)

-- Exhibit the four stopping positions in the transaction list.
-- The worst shortage occurs before the final deposit; the largest
-- required headroom occurs after it. The empty prefix is admissible.
start : M.Prefix sample (pos 0)
start = M.empty
after-credit : M.Prefix sample (pos 2)
after-credit = M.extend M.empty
after-debit : M.Prefix sample (negsuc 2)
after-debit = M.extend (M.extend M.empty)
after-final : M.Prefix sample (pos 4)
after-final = M.extend (M.extend (M.extend M.empty))

-- Read the intermediate states of the right fold, in processing order.
-- For the suffix [-5,+7] the prefixes are 0,-5,2. A greedy pass in
-- one order retains -5; the reversed comparison retains 2.
suffix = negsuc 4 ∷ pos 7 ∷ []
floors : (fst (Floor.run (pos 7 ∷ [])) ∷ fst (Floor.run suffix) ∷ fst (Floor.run sample) ∷ []) ≡ pos 0 ∷ negsuc 4 ∷ negsuc 2 ∷ []
floors = refl
ceilings : (fst (Ceiling.run (pos 7 ∷ [])) ∷ fst (Ceiling.run suffix) ∷ fst (Ceiling.run sample) ∷ []) ≡ pos 7 ∷ pos 2 ∷ pos 4 ∷ []
ceilings = refl
