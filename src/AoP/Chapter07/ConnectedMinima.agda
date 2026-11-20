{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ConnectedMinima where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Relations
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 7.20. A minimum precedes every member, in particular
-- every challenger. Conversely connectedness lets minimality handle
-- the case in which a challenger precedes the candidate.
module Law {A : Set} (R : A ← A) where
  minimal : ∀ {a X} → Min R a X → Min (Test R) a X
  minimal (xa , best) = xa , λ b xb _ → best b xb

  minimum : (∀ a b → R a b ⊎ R b a) → ∀ {a X} → Min (Test R) a X → Min R a X
  minimum connected {a} (xa , check) = xa , lower
    where lower : ∀ b → _ → R a b
          lower b xb with connected a b
          ... | inl ab = ab
          ... | inr ba = check b xb ba

-- Connectedness alone suffices. This reflexive three-cycle therefore
-- has identical minimum and minimal predicates on every subset despite
-- failing transitivity. The preorder condition cannot be inferred.
data P : Set where x y z : P
data Cycle : P ← P where
  same : ∀ {a} → Cycle a a
  xy : Cycle x y
  yz : Cycle y z
  zx : Cycle z x

total : ∀ a b → Cycle a b ⊎ Cycle b a
total x x = inl same
total x y = inl xy
total x z = inr zx
total y x = inr xy
total y y = inl same
total y z = inl yz
total z x = inl zx
total z y = inr yz
total z z = inl same

not-transitive : (Cycle ∘ Cycle ⊆ Cycle) → ⊥
not-transitive tr with tr (y , xy , yz)
... | ()
