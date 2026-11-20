{-# OPTIONS --safe --without-K #-}
module AoP.PowerLargestOutput where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Power using (ℙ; ℰ)
open import AoP.PowerRelator using (Lift)
open import Agda.Builtin.Bool

-- The domain guard in 5.16 has an exact meaning. For a fixed input
-- subset X, the lift admits an output precisely when every member
-- has a successor. In that case direct image is the largest output.
module At {A B : Set} (R : B ← A) (X : ℙ A) where
  Live = ∀ a → X a → Σ _ (λ b → R b a)
  necessary : ∀ {Y} → Lift R Y X → Live
  necessary p a x with Lift.forward p a x
  ... | b , _ , r = b , r
  full : Live → Lift R (ℰ R X) X
  Lift.backward (full live) b (a , r , x) = a , x , r
  Lift.forward (full live) a x with live a x
  ... | b , r = b , (a , r , x) , r
  largest : ∀ {Y} → Lift R Y X → ∀ b → Y b → ℰ R X b
  largest p b y with Lift.backward p b y
  ... | a , x , r = a , r , x

-- Both Boolean outputs are possible at the sole input. Keeping only
-- true still covers that input, while its direct image also has false.
module Choice where
  step : Bool ← ⊤
  step _ _ = ⊤
  input : ℙ ⊤
  input _ = ⊤
  chosen : Lift step (λ b → b ≡ true) input
  Lift.backward chosen b refl = tt , tt , tt
  Lift.forward chosen tt x = true , refl , tt
  extra : ℰ step input false
  extra = tt , tt , tt
  data Empty : Set where
  missing : false ≡ true → Empty
  missing ()
