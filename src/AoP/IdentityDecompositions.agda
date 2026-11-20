{-# OPTIONS --safe --without-K #-}
module AoP.IdentityDecompositions where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_)
open import AoP.Thinning using (Pred; Thin; Min; thin-id)
open import AoP.ThinIdentity using (preserve)

-- Exercise 9.1. In Theorem 9.2 take equality as the preorder on
-- decompositions. A retained set then contains exactly the original
-- choices. Push this equivalence through evaluation and minimization;
-- this works even when there is no decomposition or no minimum.
module At {D V : Set} (R : V ← V) (unit : ∀ v → R v v)
          (outcome : V ← D) (all : Pred D) where
  values : Pred D → Pred V
  values X v = Σ D λ d → X d × outcome v d
  Plain = Min R
  -- The simulation side condition: equal decompositions can replay
  -- the same outcome, and reflexivity compares its score with itself.
  simulate : ∀ {d e v} → d ≡ e → outcome v d → Σ V λ w → outcome w e × R w v
  simulate refl p = _ , p , unit _

  forget : ∀ {X v} → Thin _≡_ X all → Plain v (values X) → Plain v (values all)
  forget th ((d , x , p) , best) = (d , fst (preserve th) d x , p) , λ w → λ where
    (e , y , q) → best w (e , snd (preserve th) e y , q)
  retain-all : ∀ {v} → Plain v (values all) → Σ (Pred D) λ X → Thin _≡_ X all × Plain v (values X)
  retain-all p = all , thin-id (λ _ → refl) , p

-- Equal recurrence bodies have the same least prefixpoints. Apply
-- each leastness rule to the other solution after transferring its
-- closure proof pointwise; no equality of functions is needed.
module Least {I V : Set} (P Q : V ← I → V ← I)
             (forget : ∀ X → Q X ⊆ P X) (retain : ∀ X → P X ⊆ Q X)
             (p q : V ← I) (pc : P p ⊆ p) (qc : Q q ⊆ q)
             (pl : ∀ X → P X ⊆ X → p ⊆ X) (ql : ∀ X → Q X ⊆ X → q ⊆ X) where
  same : (p ⊆ q) × (q ⊆ p)
  same = pl q (λ x → qc (retain q x)) , ql p (λ x → pc (forget p x))
