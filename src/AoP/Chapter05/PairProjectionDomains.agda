{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PairProjectionDomains where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.DomainPullback using (dom)
open import AoP.Chapter05.RelationalPairing using (pair)

-- §5.2, (5.6)–(5.7). Projecting a pair discards a value but does
-- not remove the obligation to produce it. The other branch's domain
-- test records exactly that obligation, even on empty output types.
module Columns {A B C : Set} (R : B ← A) (S : C ← A) where
  left : graph fst ∘ pair R S ⊆ R ∘ dom S
  left ((b , c) , refl , r , s) = _ , r , refl , c , s
  left-back : R ∘ dom S ⊆ graph fst ∘ pair R S
  left-back (_ , r , refl , c , s) = (_ , c) , refl , r , s
  right : graph snd ∘ pair R S ⊆ S ∘ dom R
  right ((b , c) , refl , r , s) = _ , s , refl , b , r
  right-back : S ∘ dom R ⊆ graph snd ∘ pair R S
  right-back (_ , s , refl , b , r) = (b , _) , refl , r , s

  -- Dropping the domain test is justified if the discarded branch
  -- can always supply an output, or merely at inputs admitted by R.
  unrestricted : (∀ {a b} → R b a → Σ C (λ c → S c a)) → R ⊆ graph fst ∘ pair R S
  unrestricted choose r with choose r
  ... | c , s = left-back (_ , r , refl , c , s)
  necessary : R ⊆ graph fst ∘ pair R S → ∀ {a b} → R b a → Σ C (λ c → S c a)
  necessary inc r with left (inc r)
  ... | _ , _ , refl , c , s = c , s
