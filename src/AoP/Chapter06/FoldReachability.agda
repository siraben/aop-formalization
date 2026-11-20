{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FoldReachability where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)
private variable A B : Set

-- Exercise 6.7, for list algebras with a common base. Only states
-- reachable by folding the suffix need to simulate the next step.
module Bound (E : B → Set) (R S : B ← (A × B))
             (on-tail : ∀ {a b c xs} → Fold E S b xs → R c (a , b) → S c (a , b)) where
  refine : Fold E R ⊆ Fold E S
  refine (nil e) = nil e
  refine (cons step tail) with refine tail
  ... | p = cons (on-tail p step) p

-- Start at false. R permits both Boolean self-loops; S permits only
-- the false loop. The extra true loop can never be used by the fold.
base : Bool → Set
base b = b ≡ false
R S : Bool ← (⊤ × Bool)
R c p = c ≡ snd p
S c p = (c ≡ false) × (snd p ≡ false)

stays : ∀ {b xs} → Fold base S b xs → b ≡ false
stays (nil e) = e
stays (cons (c-false , _) _) = c-false

fold-inclusion : Fold base R ⊆ Fold base S
fold-inclusion = Bound.refine base R S (λ p eq → (eq ∙ stays p) , stays p)

no-step-inclusion : (R ⊆ S) → ⊥
no-step-inclusion sub with fst (sub {true} {tt , true} refl)
... | ()
