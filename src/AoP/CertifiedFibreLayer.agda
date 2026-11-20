{-# OPTIONS --safe --without-K #-}
module AoP.CertifiedFibreLayer where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Thinning using (Thin)
open import AoP.Shunting using (graph)
import AoP.FibreGeneration as Gen
import AoP.FibreGenerationTransport as Transport

-- A layer t contains only inputs for which pruning was certified.
-- Transfer its certificate through the projection; no assumption
-- that every possible input was already certified is needed.
module Law {A B : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L (P ∘ Q) ⊆ L P ∘ L Q)
  (Q : B ← B) (S : B ← F B) (simulate : S ∘ L (Q ˘) ⊆ Q ˘ ∘ S)
  (X Y : B ← A) where
  Good = Σ A λ a → Thin Q (λ b → X b a) (λ b → Y b a)
  val : Good → A
  val = fst
  children : ∀ g → Thin Q (λ b → (X ∘ graph val) b g) (λ b → (Y ∘ graph val) b g)
  Thin.subset (children g) (_ , x , refl) = _ , Thin.subset (snd g) x , refl
  Thin.cover (children g) b (_ , y , refl) with Thin.cover (snd g) b y
  ... | v , x , le = v , (_ , x , refl) , le
  module At (project : F Good → F A) (intro : graph project ⊆ L (graph val)) (elim : L (graph val) ⊆ graph project) where
    open Transport.Law {B = B} F L val project intro elim join split
    lifted = Gen.Law.generate F L mono split Q S simulate (X ∘ graph val) (Y ∘ graph val) children
    generation : ∀ t → Thin Q (λ b → (S ∘ L X) b (project t)) (λ b → (S ∘ L Y) b (project t))
    Thin.subset (generation t) (u , s , x) with Thin.subset (lifted t) (u , s , enter X x)
    ... | v , r , y = v , r , exit Y y
    Thin.cover (generation t) b (v , s , y) with Thin.cover (lifted t) b (v , s , enter Y y)
    ... | z , (u , r , x) , le = z , (u , r , exit X x) , le
