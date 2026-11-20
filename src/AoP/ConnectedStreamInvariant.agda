{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedStreamInvariant where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.ConnectedBlock using (module Law)
open import AoP.ConnectedPartitionFusion using (module Fusion)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Subsequences using (here; there)

-- Exercise 8.14. Verify the greedy boundary test on every reachable
-- block. A failed comparison rules out adjoining the next letter to
-- this block, rather than merely failing a sufficient test.
module Invariant {A : Set} (Q : A → A → Set) (self : ∀ x → Q x x)
  (trans : ∀ {x y z} → Q x y → Q y z → Q x z)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Fusion Q self trans test
  open Law Q using (Connected) renaming (extend to connected-cons)
  open import AoP.LongestConnectedBlock using (module Scan)
  open Scan Q self test using (Cross; cross?)
  open import AoP.Complement using (⊥)
  Good : Block → Set
  Good b = Connected (Block.xs b)
  single : ∀ a → Good (one a)
  single a _ _ here here = inl (self a)
  single a _ _ here (there ())
  single a _ _ (there ()) _
  grow : ∀ a b (cmp : Cross a (Block.xs b)) → Good b → Good (extend a b cmp)
  grow a b cmp ok with cmp (Block.m b) (Block.member b)
  ... | inl _ = connected-cons (self a) cmp ok
  ... | inr _ = connected-cons (self a) cmp ok
  barrier : ∀ a b → (Cross a (Block.xs b) → ⊥) → Connected (a ∷ Block.xs b) → ⊥
  barrier a b no ok = no (λ y m → ok a y here (there m))
  All : Snoc Block → Set
  All ε = ⊤
  All (ds ▻ b) = All ds × Good b
  Valid : State Block → Set
  Valid empty = ⊤
  Valid (active ds b) = All ds × Good b
  preserve : ∀ s a → Valid s → Valid (advance (λ x → x) s a)
  preserve empty a _ = tt , single a
  preserve (active ds b) a (prev , ok) with cross? a (Block.xs b)
  ... | inl cmp = prev , grow a b cmp ok
  ... | inr no = (prev , ok) , single a
  reachable : ∀ t → Valid (partition t)
  reachable ε = tt
  reachable (t ▻ a) = preserve (partition t) a (reachable t)
