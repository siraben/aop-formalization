{-# OPTIONS --safe --without-K #-}
module AoP.InitialSingletonThinning where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Shunting using (graph)
open import AoP.Thinning using (Min; Thin; thin-compose)
import AoP.SingletonThinning as Single
import AoP.CertifiedFibreLayer as Cert

-- Exercise 8.8: specialize the table at each input to {pick input}.
-- The singleton-elimination law turns a local minimum into the pruning
-- step. Projection from certified inputs and initiality iterate it.
module Proof (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Theory F
  open Initial I
  open Functor F using () renaming (F₀ to Layer; F₁ to map)
  module Law {B : Set} (L : ∀ {U V} → V ← U → Layer V ← Layer U)
    (mono : ∀ {U V} (P Q : V ← U) → P ⊆ Q → L P ⊆ L Q)
    (join : ∀ {U V W} (P : W ← V) (Q : V ← U) → L P ∘ L Q ⊆ L (P ∘ Q))
    (split : ∀ {U V W} (P : W ← V) (Q : V ← U) → L (P ∘ Q) ⊆ L P ∘ L Q)
    (intro : ∀ {U V} (f : U → V) → graph (map f) ⊆ L (graph f))
    (elim : ∀ {U V} (f : U → V) → L (graph f) ⊆ graph (map f))
    (Q : B ← B) (trans : ∀ {a b c} → Q a b → Q b c → Q a c)
    (S : B ← Layer B) (sim : S ∘ L (Q ˘) ⊆ Q ˘ ∘ S)
    (pick : μ → B) (full : B ← μ) where
    X : B ← μ
    X b x = b ≡ pick x
    module G = Cert.Law Layer L mono join split Q S sim X full
    open G.At (map G.val) (intro G.val) (elim G.val) using (generation)
    module Run (roll : ∀ t b → (S ∘ L full) b t → full b (inn t))
      (unroll : ∀ t b → full b (inn t) → (S ∘ L full) b t)
      (local : ∀ t → Min Q (pick (inn t)) (λ b → (S ∘ L X) b t)) where
      algebra : Algebra G.Good
      algebra t = inn u , thin-compose trans (Single.Law.eliminate Q _ _ (local u)) cover
        where u = map G.val t
              cover : Thin Q (λ b → (S ∘ L X) b u) (λ b → full b (inn u))
              Thin.subset cover p = roll u _ (Thin.subset (generation t) p)
              Thin.cover cover b p = Thin.cover (generation t) b (unroll u b p)
      minimum : ∀ x → Min Q (pick x) (λ b → full b x)
      minimum x = shift eq (Single.Law.minimum Q _ _ (snd (⦅ algebra ⦆ x)))
        where
        rev : ∀ {a b : μ} → a ≡ b → b ≡ a
        rev refl = refl
        eq : G.val (⦅ algebra ⦆ x) ≡ x
        eq = Laws.fusion I algebra inn G.val (λ _ → refl) x ∙ rev (Laws.reflection I x)
        shift : ∀ {a b : μ} → a ≡ b → Min Q (pick a) (λ v → full v a) → Min Q (pick b) (λ v → full v b)
        shift refl m = m
