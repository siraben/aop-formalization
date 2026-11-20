{-# OPTIONS --safe --without-K #-}
module AoP.GraphInclusionTrace where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Relations using (_←_; _∘_)
open import AoP.PartialGraphCategory using (Partial; partial; module Partial)
open import AoP.TotalPartialEmbedding using (total)
open import AoP.Categories using (Category)
open import AoP.RelationGraphCategory using (Rel)
open import Agda.Builtin.Bool using (Bool; false; true)

-- §2.1. Inspect the same Boolean input in the three categories.
-- A partial identity accepts only true. No total Boolean function can
-- have this graph: it would have to return some value at false.
data Guard : Bool ← Bool where
  accept : Guard true true
one : Partial Bool Bool
one = partial Guard λ { accept accept → refl }
no-total : (f : Bool → Bool) → Category._≈_ Rel (Partial.edge (total f)) Guard → ⊥
no-total f eq = absent (fst eq {a = false} refl)
  where absent : ∀ {b} → Guard b false → ⊥
        absent ()

-- The next arrow can produce either bit. After the guard there are
-- two paths from true, each through true; from false there are none.
Both : Bool ← Bool
Both b a = ⊤
choices : ((Both ∘ Guard) false true) × ((Both ∘ Guard) true true)
choices = (true , (tt , accept)) , (true , (tt , accept))
reject : ∀ b → (Both ∘ Guard) b false → ⊥
reject b (i , (_ , ()))
no-partial : (p : Partial Bool Bool) → Category._≈_ Rel (Both ∘ Guard) (Partial.edge p) → ⊥
no-partial p eq = distinct (Partial.single p (fst eq (fst choices)) (fst eq (snd choices)))
  where distinct : false ≡ true → ⊥
        distinct ()
