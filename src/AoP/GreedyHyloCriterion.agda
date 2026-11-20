{-# OPTIONS --safe --without-K #-}
module AoP.GreedyHyloCriterion where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)
open import AoP.Thinning using (Min)

-- Theorem 7.2 and exercise 7.36. G and E are the greedy and
-- exhaustive folds of the local minimum and the candidate algebra S.
-- Their joint runs form the hylomorphism H. The hypotheses below are
-- its computation/leastness laws and feasibility of the greedy fold.
module Law {A T : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (R : A ← A) (S : A ← F A) (G E : A ← T) (feasible : G ⊆ E) where
  M : A ← F A
  M a t = Min R a (λ b → S b t)
  H = G ∘ E ˘
  layer : A ← A → A ← A
  layer X = M ∘ (L X ∘ S ˘)
  Winner : Set
  Winner = ∀ {a t} → G a t → Min R a (λ b → E b t)
  module Fixed (roll : layer H ⊆ H) (least : ∀ X → layer X ⊆ X → H ⊆ X) where
    -- Guard comparisons with an actual pair of runs on a common child
    -- input. This gives an inductive invariant R ∩ H, and using H
    -- avoids imposing obligations on unreachable competitors.
    Guard = R ⊓ H
    Local = layer Guard ⊆ R
    necessary : Winner → Local
    necessary win (u , m , v , related , rival) with roll (u , m , v , mono Guard H snd related , rival)
    ... | t , g , e = snd (win g) _ e
    sufficient : Local → Winner
    sufficient test {t = t} g = feasible g , λ b e → fst (least Guard closed (t , g , e))
      where closed : layer Guard ⊆ Guard
            closed step@(u , m , v , related , rival) = test step , roll (u , m , v , mono Guard H snd related , rival)
    -- The usual global monotonicity condition simulates the rival at
    -- the greedy child layer. Compare the local minimum with that
    -- feasible result and then use transitivity to reach the rival.
    greedy : (∀ {a b c} → R a b → R b c → R a c) → L R ∘ S ˘ ⊆ S ˘ ∘ R → Winner
    greedy trans sim = sufficient local
      where local : Local
            local (u , m , v , related , rival) with sim (v , mono Guard R fst related , rival)
            ... | b , allowed , le = trans (snd m b allowed) le
