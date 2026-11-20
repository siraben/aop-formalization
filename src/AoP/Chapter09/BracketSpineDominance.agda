{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketSpineDominance where

open import AoP.Common.Prelude
open import AoP.Chapter09.Bracketing using (module Model)
open import AoP.Chapter09.BracketSpine using (Place; root; descend)
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Common.NatOrder using (_≤_; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 9.14. Future prepends can open the left spine but never
-- the right subtrees already hanging from it. Compare those sealed
-- subtrees by equal size and no greater cost, at each spine position.
module Law {A S : Set} (atom : A → S) (combine : S → S → S) (charge : S → S → Nat) where
  open Model atom combine charge using (size; cost)
  Closed : Tree A → Tree A → Set
  Closed t u = (size t ≡ size u) × (cost t ≤ cost u)
  data Spine : Tree A → Tree A → Set where
    leaf : ∀ {x y} → atom x ≡ atom y → Spine (tip x) (tip y)
    fork : ∀ {l r l′ r′} → Spine l l′ → Closed r r′ → Spine (bin l r) (bin l′ r′)
  close : ∀ {t u} → Spine t u → Closed t u
  close (leaf eq) = eq , rid _
  close (fork {l} {r} {l′} {r′} p (e , le)) with close p
  ... | f , q rewrite f | e = refl , sum-mono (rid (charge (size l′) (size r′))) (sum-mono q le)

  -- Every insertion into the discarded tree can be matched at exactly
  -- the same depth in the retained tree. The new trees still compare.
  simulate : ∀ {a t u v} → Spine t u → Place a u v → Σ (Tree A) λ w → Place a t w × Spine w v
  simulate p root = _ , root , fork (leaf refl) (close p)
  simulate (fork l r) (descend i) with simulate l i
  ... | w , place , p = _ , descend place , fork p r
