{-# OPTIONS --safe --without-K #-}
module AoP.ObjectiveThinning where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Thinning using (Min)

-- Exercise 9.4. Good and bad subproblems are compared by witnesses
-- for their optimal outcomes. A bad outcome need not itself be optimal:
-- first bound it by the bad optimum, then by the good optimum.
module Compare {A V : Set} (H : V ← A) (R : V ← V)
               (trans : ∀ {u v w} → R u v → R v w → R u w) where
  M : V ← A
  M v x = Min R v (λ w → H w x)
  C : A ← A
  C = M ˘ ∘ (R ∘ M)
  replay : H ∘ C ˘ ⊆ R ˘ ∘ H
  replay (bad , outcome , goodBest , (feasible , _) , badBest , better , (_ , bounds)) =
    goodBest , trans better (bounds _ outcome) , feasible

  -- Reflexivity requires an attainable optimum at the subproblem.
  -- Transitivity works even if the middle optimum is not unique.
  reflexive : (∀ v → R v v) → ∀ {x v} → M v x → C x x
  reflexive unit {v = v} m = v , m , v , unit v , m
  composeC : ∀ {x y z} → C x y → C y z → C x z
  composeC (a , ma , b , ab , mb) (c , mc , d , cd , md) =
    a , ma , d , trans ab (trans (snd mb c (fst mc)) cd) , md

  -- Lift the replay through F using only the composition, converse
  -- and inclusion laws. The outer objective h is monotone on R.
  module Layer (F : Set → Set) (lift : ∀ {A B} → B ← A → F B ← F A)
    (join : ∀ {A B D} (P : D ← B) (Q : B ← A) → lift P ∘ lift Q ⊆ lift (P ∘ Q))
    (split : ∀ {A B D} (P : D ← B) (Q : B ← A) → lift (P ∘ Q) ⊆ lift P ∘ lift Q)
    (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → lift P ⊆ lift Q)
    (conv : ∀ {A B} (P : B ← A) → (lift P) ˘ ⊆ lift (P ˘))
    (h : F V → V) (hm : ∀ {x y} → lift (R ˘) x y → R (h y) (h x)) where
    Q = lift C
    match : ∀ {good bad v} → Q good bad → lift H v bad → Σ (F V) λ w → lift H w good × R (h w) (h v)
    match {bad = bad} q old with split (R ˘) H (mono (H ∘ C ˘) (R ˘ ∘ H) replay (join H (C ˘) (bad , old , conv C q)))
    ... | w , le , ok = w , ok , hm le
