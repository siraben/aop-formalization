{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PairPullInstance where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (graph; Id)
open import AoP.Chapter05.RelationalProducts using (_⊗_)
open import AoP.Chapter05.ModularPairPull using (module In)
open import AoP.Chapter05.ConcreteAllegory using (laws)

-- Instantiate the modular proof, checking both projection claims
-- directly. No assumption that the changed branch is functional.
module Step {A B Y : Set} (R : B ← A) where
  la = graph (fst {A = A} {B = λ _ → Y})
  lb = graph (fst {A = B} {B = λ _ → Y})
  ra = graph (snd {A = A} {B = λ _ → Y})
  rb = graph (snd {A = B} {B = λ _ → Y})
  t = R ⊗ Id {A = Y}
  -- The unchanged coordinate of the pair supplies the missing value.
  send : lb ˘ ∘ R ⊆ t ∘ la ˘
  send {b = (b , y)} (_ , refl , r) = (_ , y) , (r , refl) , refl
  back : t ∘ la ˘ ⊆ lb ˘ ∘ R
  back ((_ , _) , (r , refl) , refl) = _ , refl , r
  -- Forget the R witness; the identity edge fixes the right value.
  keep : t ˘ ∘ rb ˘ ⊆ ra ˘
  keep ((_ , _) , (r , refl) , refl) = refl
  module Derivation = In.Step laws la ra lb rb R t (send , back) keep
