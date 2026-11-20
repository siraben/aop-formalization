{-# OPTIONS --safe --without-K #-}
module AoP.InitialFibrePruning where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)
open import AoP.Thinning using (Pred; Thin; Min; thin-compose; min-after-thin)
open import AoP.PowerRelator using (Lift)
open import AoP.FibrePowerThinning using (module Law)

-- Exercise 8.11. A layer of certified child tables has two tasks:
-- simulate exhaustive generation from retained children, then thin
-- those reachable results by selecting minima in intermediate fibres.
module Proof (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Theory F
  open Initial I
  open Functor F using () renaming (F₀ to Layer; F₁ to map)
  module Tables {B K : Set} (finish : B ← K) (Q R : B ← B)
    (safe : R ⊓ (finish ∘ finish ˘) ⊆ Q) (sub : Q ⊆ R)
    (qt : ∀ {x y z} → Q x y → Q y z → Q x z)
    (rt : ∀ {x y z} → R x y → R y z → R x z)
    (table full : μ → Pred B) (enabled : Layer μ → Pred K) where
    open Law finish Q R safe
    Good = Σ μ λ x → Thin Q (table x) (full x)
    val : Good → μ
    val = fst
    module Iterate
      (generate : ∀ (t : Layer Good) → Thin Q (Reach (enabled (map val t))) (full (inn (map val t))))
      (select : ∀ t → Lift M (table (inn t)) (enabled t)) where
      algebra : Algebra Good
      algebra t = inn (map val t) , thin-compose qt (local (select (map val t))) (generate t)
      correct : ∀ x → Thin Q (table x) (full x)
      correct x = transport (forget x) (snd (⦅ algebra ⦆ x))
        where
        rev : ∀ {a b : μ} → a ≡ b → b ≡ a
        rev refl = refl
        forget : ∀ x → val (⦅ algebra ⦆ x) ≡ x
        forget x = Laws.fusion I algebra inn val (λ _ → refl) x ∙ rev (Laws.reflection I x)
        transport : ∀ {a b : μ} → a ≡ b → Thin Q (table a) (full a) → Thin Q (table b) (full b)
        transport refl proof = proof
      optimum : ∀ x {a} → Min R a (table x) → Min R a (full x)
      optimum x = min-after-thin sub rt (correct x)
