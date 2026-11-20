{-# OPTIONS --safe --without-K #-}
module AoP.PrunedDP where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)
open import AoP.Thinning using (Thin; Min; Pred)
open import AoP.PowerRelator using (Lift)

-- Theorem 9.2. T lists the legal decompositions of an input; h combines
-- a layer of solved children. H is the feasible-result relation, given
-- with the two directions of its hylomorphism equation. The candidate
-- prefixpoint M consists of globally feasible minima.
module Context {A V : Set} (F : Set → Set)
  (L : ∀ {A B} → B ← A → F B ← F A)
  (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {A B D} (P : D ← B) (Q : B ← A) → L P ∘ L Q ⊆ L (P ∘ Q))
  (conv : ∀ {A B} (P : B ← A) → (L P) ˘ ⊆ L (P ˘))
  (T : A ← F A) (h : F V → V) (H : V ← A) (R : V ← V) (Q : F A ← F A)
  (trans : ∀ {u v w} → R u v → R v w → R u w)
  (roll : ∀ {a b v} → T a b → L H v b → H (h v) a)
  (unroll : ∀ {a w} → H w a → Σ _ λ b → T a b × Σ _ λ v → L H v b × (h v ≡ w))
  (monotone : ∀ {v w} → L (R ⊓ (H ∘ H ˘)) v w → R (h v) (h w))
  (match : ∀ {b c v} → (Q ⊓ (T ˘ ∘ T)) c b → L H v b → Σ _ λ w → L H w c × R (h w) (h v)) where
  M : V ← A
  M v a = Min R v (λ w → H w a)
  Eval : V ← A → V ← F A
  Eval X w b = Σ _ λ v → (h v ≡ w) × L X v b
  Step : (V ← A) → V → A → Set₁
  Step X w a = Σ (Pred (F A)) λ Y → Σ (Pred V) λ O → Thin Q Y (T a) × Lift (Eval X) O Y × Min R w O

  -- Feasibility first; then compare the local winner to every global
  -- rival. Thinning finds a retained decomposition; power coverage
  -- supplies a selected outcome for that very decomposition.
  prefix : ∀ {w a} → Step M w a → M w a
  prefix (Y , O , t , p , inO , least) with Lift.backward p _ inO
  ... | b , y , v , refl , opt = roll (Thin.subset t y) (mono M H fst opt) , bound
    where
    below : M ∘ H ˘ ⊆ R ⊓ (H ∘ H ˘)
    below (a , m , feasible) = snd m _ feasible , a , fst m , feasible
    bound : ∀ z → H z _ → R (h v) z
    bound z feasible with unroll feasible
    ... | bad , legal , r , run , refl with Thin.cover t bad legal
    ... | good , kept , dominates with match (dominates , _ , Thin.subset t kept , legal) run | Lift.forward p good kept
    ... | s , rival , improvement | _ , selected , u , refl , best =
      trans (least _ selected) (trans (monotone (mono (M ∘ H ˘) (R ⊓ (H ∘ H ˘)) below
        (join M (H ˘) (good , best , conv H rival)))) improvement)

  -- The only fixed-point rule needed is leastness among prefixpoints.
  theorem : (solution : V ← A) →
    (∀ X → (∀ {w a} → Step X w a → X w a) → solution ⊆ X) → solution ⊆ M
  theorem solution least = least M prefix

-- The global hypotheses of Theorem 9.2 imply Exercise 9.2's local
-- hypotheses by forgetting the common-input witnesses in each meet.
module Law {A V : Set} (F : Set → Set)
  (L : ∀ {A B} → B ← A → F B ← F A)
  (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {A B D} (P : D ← B) (Q : B ← A) → L P ∘ L Q ⊆ L (P ∘ Q))
  (conv : ∀ {A B} (P : B ← A) → (L P) ˘ ⊆ L (P ˘))
  (T : A ← F A) (h : F V → V) (H : V ← A) (R : V ← V) (Q : F A ← F A)
  (trans : ∀ {u v w} → R u v → R v w → R u w)
  (roll : ∀ {a b v} → T a b → L H v b → H (h v) a)
  (unroll : ∀ {a w} → H w a → Σ _ λ b → T a b × Σ _ λ v → L H v b × (h v ≡ w))
  (monotone : ∀ {v w} → L R v w → R (h v) (h w))
  (match : ∀ {b c v} → Q c b → L H v b → Σ _ λ w → L H w c × R (h w) (h v)) where
  open Context F L mono join conv T h H R Q trans roll unroll
    (λ p → monotone (mono (R ⊓ (H ∘ H ˘)) R fst p)) (λ q → match (fst q)) public
