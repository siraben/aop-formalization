{-# OPTIONS --safe --without-K #-}
module AoP.ReserveFoldAgreement where

open import AoP.Prelude
open import AoP.Reserves using (Tx; deposit; withdraw)
open import AoP.ReserveExtrema using (Needs; need; summary; extend)
open import AoP.ReserveClipping
open import AoP.ReserveGrowth
open import AoP.ReserveGreedyClip
open import AoP.ReservePrefixWitness using (floor; ceiling)
open import AoP.ReservePrefixGreedy using (module Floor; module Ceiling)
open import AoP.SignedSegment using (module M)
open import AoP.Horner using (map)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; suc)

signed : Tx → Int
signed (deposit n) = pos n
signed (withdraw 0) = pos 0
signed (withdraw (suc n)) = negsuc n

pair : List Int → Needs
pair ts = need (stock (fst (Floor.run ts))) (space (fst (Ceiling.run ts)))
private
  both : ∀ {x y a b : Nat} → x ≡ a → y ≡ b → need x y ≡ need a b
  both refl refl = refl

step : ∀ t ts → pair (signed t ∷ ts) ≡ extend t (pair ts)
step (deposit n) ts = both (floor-step (pos n) ts ∙ release-stock n _) (ceiling-step (pos n) ts ∙ require-space n _ (snd (ceiling ts) _ M.empty))
step (withdraw 0) ts = both (floor-step (pos 0) ts) (ceiling-step (pos 0) ts)
step (withdraw (suc n)) ts = both (floor-step (negsuc n) ts ∙ require-stock (suc n) _ (snd (floor ts) _ M.empty)) (ceiling-step (negsuc n) ts ∙ release-space (suc n) _)

agreement : ∀ ts → pair (map signed ts) ≡ summary ts
agreement [] = refl
agreement (t ∷ ts) = step t (map signed ts) ∙ cong (extend t) (agreement ts)
