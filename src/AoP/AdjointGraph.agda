{-# OPTIONS --safe --without-K #-}
module AoP.AdjointGraph where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_; _˘)
open import AoP.InjectionAdjunction using (module Adj)
open import AoP.Shunting using (Id; graph; Map)

-- Proposition 4.1 in concrete Rel: extract the function represented by
-- the left adjoint. The unit already contains an intermediate output,
-- so extracting it needs no separate choice principle. The counit
-- identifies every other output at this input with the extracted one.
module Extract {A B : Set} (R : B ← A) (S : A ← B)
  (unit : Id ⊆ S ∘ R) (counit : R ∘ S ⊆ Id) where
  module Converse = Adj R S unit counit
  run : A → B
  run a = fst (unit {a = a} refl)
  edge : ∀ a → R (run a) a
  edge a = snd (snd (unit {a = a} refl))
  complete : R ⊆ graph run
  complete {a = a} r = counit (a , edge a , Converse.backward r)
  sound : graph run ⊆ R
  sound {a = a} refl = edge a
  represented : Map R
  Map.entire represented {a = a} refl = run a , edge a , edge a
  Map.simple represented (a , r , q) = counit (a , r , Converse.backward q)
