{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.SecurePartitionFold where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_; module Layout)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter07.VanSchedule using (module Schedule)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 7.51. Push the security test into the partition fold.
-- Starting a block checks the singleton; extending checks only the
-- enlarged block. Recover the old block by dropping the first posting.
module Law (capacity : Nat) where
  open Bank capacity
  open Schedule capacity using (Block; Plan; feasible; Valid)
  open Layout (λ (_ : Tx) → 0) 0 using (new; glue)
  open Breaks (λ (_ : Tx) → 0) 0 using (Partition; single; break-before-tail; continue-line)
  safe : Block → Set
  safe (v ∷⁺ vs) = Secure (v ∷ vs)
  head : ∀ l ls → feasible l ls → safe l
  head (v ∷⁺ vs) [] f = f
  head (v ∷⁺ vs) (_ ∷ _) f = fst f
  replace : ∀ l k ls → safe k → feasible l ls → feasible k ls
  replace (v ∷⁺ vs) (w ∷⁺ ws) [] ok _ = ok
  replace (v ∷⁺ vs) (w ∷⁺ ws) (_ ∷ _) ok f = ok , snd f
  tail-secure : ∀ {v vs} → Secure (v ∷ vs) → Secure vs
  tail-secure (_ , b , post _ _ rest) = _ , b , rest

  data Generated : Tx → List Tx → Plan → Set where
    base : ∀ w → Secure (w ∷ []) → Generated w [] ((w ∷⁺ []) ∷⁺ [])
    fresh : ∀ {v vs p} w → Secure (w ∷ []) → Generated v vs p → Generated w (v ∷ vs) (new w p)
    extend : ∀ {v vs l ls} w → Secure (w ∷ Nonempty.first l ∷ Nonempty.rest l) → Generated v vs (l ∷⁺ ls) → Generated w (v ∷ vs) (glue w (l ∷⁺ ls))

  sound : ∀ {w ws p} → Generated w ws p → Partition w ws p × Valid p
  sound (base w f) = single w , f
  sound (fresh {p = (v ∷⁺ vs) ∷⁺ ls} w ok g) with sound g
  ... | p , f = break-before-tail w p , ok , f
  sound (extend {l = v ∷⁺ vs} {ls} w ok g) with sound g
  ... | p , f = continue-line w p , replace (v ∷⁺ vs) (w ∷⁺ (v ∷ vs)) ls ok f

  complete : ∀ {w ws p} → Partition w ws p → Valid p → Generated w ws p
  complete (single w) f = base w f
  complete (break-before-tail {p = (v ∷⁺ vs) ∷⁺ ls} w p) (ok , f) = fresh w ok (complete p f)
  complete (continue-line {p = (v ∷⁺ vs) ∷⁺ ls} w p) f = extend w ok (complete p shorter)
    where ok = head (w ∷⁺ (v ∷ vs)) ls f
          shorter = replace (w ∷⁺ (v ∷ vs)) (v ∷⁺ vs) ls (tail-secure ok) f
