{-# OPTIONS --safe --without-K #-}
module AoP.FibreFoldRefinement where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)
open import AoP.Shunting using (graph)
open import AoP.Thinning using (Thin)
open import AoP.PowerRelator using (Lift)
import AoP.FibrePowerThinning as P
import AoP.InitialFibrePruning as Iter
import AoP.CertifiedFibreLayer as Cert

-- 8.11. Instantiate generation at the constructor: the enabled
-- intermediate states are exactly S₂ ∘ L X, and exhaustive evaluation
-- unrolls into (S₁ ∘ S₂) ∘ L Y. No generation simulation is assumed.
module Fold (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Theory F
  open Initial I
  open Functor F using () renaming (F₀ to Layer; F₁ to map)
  module Law {B K : Set} (L : ∀ {U V} → V ← U → Layer V ← Layer U)
    (mono : ∀ {U V} (P Q : V ← U) → P ⊆ Q → L P ⊆ L Q)
    (join : ∀ {U V W} (P : W ← V) (Q : V ← U) → L P ∘ L Q ⊆ L (P ∘ Q))
    (split : ∀ {U V W} (P : W ← V) (Q : V ← U) → L (P ∘ Q) ⊆ L P ∘ L Q)
    (intro : ∀ {U V} (f : U → V) → graph (map f) ⊆ L (graph f))
    (elim : ∀ {U V} (f : U → V) → L (graph f) ⊆ graph (map f))
    (S₁ : B ← K) (S₂ : K ← Layer B) (Q R : B ← B)
    (safe : R ⊓ (S₁ ∘ S₁ ˘) ⊆ Q) (sub : Q ⊆ R)
    (qt : ∀ {x y z} → Q x y → Q y z → Q x z) (rt : ∀ {x y z} → R x y → R y z → R x z)
    (sim : (S₁ ∘ S₂) ∘ L (Q ˘) ⊆ Q ˘ ∘ (S₁ ∘ S₂)) (X Y : B ← μ) where
    enabled = S₂ ∘ L X
    table = λ t b → X b t
    full = λ t b → Y b t
    module T = Iter.Proof.Tables F I S₁ Q R safe sub qt rt table full (λ t i → enabled i t)
    module G = Cert.Law Layer L mono join split Q (S₁ ∘ S₂) sim X Y
    open G.At (map T.val) (intro T.val) (elim T.val) using (generation)
    module Run
      (roll : ∀ t b → ((S₁ ∘ S₂) ∘ L Y) b t → Y b (inn t))
      (unroll : ∀ t b → Y b (inn t) → ((S₁ ∘ S₂) ∘ L Y) b t)
      (select : ∀ t → Lift (P.Law.M S₁ Q R safe) (table (inn t)) (λ i → enabled i t)) where
      ready : ∀ t → Thin Q (P.Law.Reach S₁ Q R safe (λ i → enabled i (map T.val t))) (full (inn (map T.val t)))
      Thin.subset (ready t) (i , (u , s₂ , x) , s₁) = roll _ _ (Thin.subset (generation t) (u , (i , s₁ , s₂) , x))
      Thin.cover (ready t) b y with Thin.cover (generation t) b (unroll _ _ y)
      ... | a , (u , (i , s₁ , s₂) , x) , le = a , (i , (u , s₂ , x) , s₁) , le
      open T.Iterate ready select public using (correct; optimum)
