{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FrontierRolling where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter06.FiniteFrontierBudget using (Dec)
open import AoP.Chapter06.Closure using (module Paths)
open import AoP.Chapter06.ClosureFrontierInvariant using (module Search)

-- §6.7 (6.9). P records vertices already scanned. Grow starts at Q
-- and can extend a path only if the new destination is outside P.
-- This is the least such set, by induction on the path witness.
module Law {A : Set} (R : A ← A) where
  data Grow (P Q : A → Set) : A → Set where
    seed : ∀ {x} → Q x → Grow P Q x
    step : ∀ {x y} → Grow P Q x → R y x → (P y → ⊥) → Grow P Q y
  least : ∀ {P Q} (X : A → Set) → (∀ x → Q x → X x) →
    (∀ {x y} → X x → R y x → (P y → ⊥) → X y) → ∀ {x} → Grow P Q x → X x
  least X start extend (seed q) = start _ q
  least X start extend (step path e n) = extend (least X start extend path) e n
  Theta : (A → Set) → (A → Set) → A → Set
  Theta P Q x = P x ⊎ Grow P Q x
  -- At initialization the empty exclusion set accepts every step.
  -- At termination the empty seed set admits no growing path at all.
  module Init (Q : A → Set) where
    reachable : ∀ {x} → Theta (λ _ → ⊥) Q x → Search.Reach R Q x
    reachable (inl ())
    reachable (inr path) = least (Search.Reach R Q) (λ x q → x , q , Paths.stop) advance path
      where advance : ∀ {x y} → Search.Reach R Q x → R y x → (⊥ → ⊥) → Search.Reach R Q y
            advance (s , q , h) e _ = s , q , Paths.extend e h
    initial : ∀ {x} → Search.Reach R Q x → Theta (λ _ → ⊥) Q x
    initial (s , q , path) = inr (walk path)
      where walk : ∀ {x} → Paths.Star R x s → Grow (λ _ → ⊥) Q x
            walk Paths.stop = seed q
            walk (Paths.extend e h) = step (walk h) e (λ z → z)
  module Stop (P : A → Set) where
    finish : ∀ {x} → Theta P (λ _ → ⊥) x → P x
    finish (inl p) = p
    finish (inr path) with least (λ _ → ⊥) (λ _ z → z) (λ z _ _ → z) path
    ... | ()
    include : ∀ {x} → P x → Theta P (λ _ → ⊥) x
    include = inl
  module Round (P Q : A → Set) (dq : ∀ x → Dec (Q x)) where
    Seen = λ x → P x ⊎ Q x
    Fresh = λ y → (Σ A (λ x → Q x × R y x)) × (Seen y → ⊥)
    -- When a path revisits Q, restart there. After its last visit,
    -- the next edge starts a fresh path and later edges extend it.
    split : ∀ {x} → Grow P Q x → Q x ⊎ Grow Seen Fresh x
    split (seed q) = inl q
    split (step {y = y} path e np) with dq y
    ... | inl q = inl q
    ... | inr nq with split path
    ...   | inl q = inr (seed ((_ , q , e) , λ { (inl p) → np p ; (inr v) → nq v }))
    ...   | inr tail = inr (step tail e λ { (inl p) → np p ; (inr v) → nq v })
    forward : ∀ {x} → Theta P Q x → Theta Seen Fresh x
    forward (inl p) = inl (inl p)
    forward (inr path) with split path
    ... | inl q = inl (inr q)
    ... | inr tail = inr tail
    -- Undo a fresh seed by restoring its first edge out of Q.
    restore : ∀ {x} → Grow Seen Fresh x → Grow P Q x
    restore (seed ((x , q , e) , n)) = step (seed q) e (λ p → n (inl p))
    restore (step path e n) = step (restore path) e (λ p → n (inl p))
    backward : ∀ {x} → Theta Seen Fresh x → Theta P Q x
    backward (inl (inl p)) = inl p
    backward (inl (inr q)) = inr (seed q)
    backward (inr tail) = inr (restore tail)
