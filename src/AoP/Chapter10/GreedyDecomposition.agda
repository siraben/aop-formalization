{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.GreedyDecomposition where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Chapter08.Thinning using (Min)

-- §10.1, Theorem 10.1 in Rel. T a b permits layer b at input a.
-- H is the exhaustive result relation. Choose a Q-minimum split
-- *before* recursively solving children; the proof does not demand
-- that every fibre has a Q-minimum or that a minimum is unique.
module Law {A V : Set} (F : Set → Set)
  (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (conv : ∀ {X Y} (P : Y ← X) → (L P) ˘ ⊆ L (P ˘))
  (T : A ← F A) (h : F V → V) (H : V ← A) (R : V ← V) (Q : F A ← F A)
  (trans : ∀ {u v w} → R u v → R v w → R u w)
  (roll : ∀ {a b v} → T a b → L H v b → H (h v) a)
  (unroll : ∀ {a w} → H w a → Σ _ λ b → T a b × Σ _ λ v → L H v b × (h v ≡ w))
  (ordered : ∀ {v w} → L R v w → R (h v) (h w))
  (exchange : ∀ {b c v} → Q c b → L H v b → Σ _ λ w → L H w c × R (h w) (h v)) where
  M : V ← A
  M v a = Min R v (λ y → H y a)
  Step : V ← A → V ← A
  Step X v a = Σ _ λ c → Min Q c (T a) × Σ _ λ u → L X u c × (h u ≡ v)

  -- Minimizing each child bounds every feasible completion at the
  -- same split. The common intermediate layer c witnesses composition.
  children : ∀ {u w c} → L M u c → L H w c → R (h u) (h w)
  children {c = c} best feasible = ordered (mono (M ∘ H ˘) R
    (λ { (_ , child-min , rival) → snd child-min _ rival })
    (join M (H ˘) (c , best , conv H feasible)))

  prefix : Step M ⊆ M
  prefix (c , (permitted , first) , u , best , refl) =
    roll permitted (mono M H fst best) , lower
    where
    open BoundSteps R trans
    lower : ∀ z → H z _ → R (h u) z
    lower z rival with unroll rival
    ... | b , legal , v , run , refl with exchange (first b legal) run
    ... | w , completion , bound =
      h u ≤⟨ children best completion ⟩
      h w ≤⟨ bound ⟩∎ h v

  theorem : (solution : V ← A) → (∀ X → Step X ⊆ X → solution ⊆ X) → solution ⊆ M
  theorem solution least = least M prefix
