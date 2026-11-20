{-# OPTIONS --safe --without-K #-}
module AoP.RelationalFrontierRolling where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Closure using (module Paths)
open import AoP.FrontierRolling using (module Law)
open import AoP.FiniteFrontierBudget using (Dec)

-- Equation (6.9) on relations: every column is a separate search.
-- The input b remains fixed through the recursive paths; forgetting
-- this would mix paths discovered from different starting columns.
module Derive {A B : Set} (R : A ← A) where
  open Law R
  zero : A ← B
  zero _ _ = ⊥
  θ : A ← B → A ← B → A ← B
  θ P Q a b = Theta (λ x → P x b) (λ x → Q x b) a
  module Initial (S : A ← B) where
    forward : θ zero S ⊆ Paths.Star R ∘ S
    forward {a} {b} t with Init.reachable (λ x → S x b) t
    ... | x , seed-edge , path = x , path , seed-edge
    backward : Paths.Star R ∘ S ⊆ θ zero S
    backward {a} {b} (x , path , seed-edge) = Init.initial (λ y → S y b) (x , seed-edge , path)
  module Empty (P : A ← B) where
    finish : θ P zero ⊆ P
    finish {a} {b} = Stop.finish (λ x → P x b)
    include : P ⊆ θ P zero
    include = inl
  module Advance (P Q : A ← B) (test : ∀ a b → Dec (Q a b)) where
    Seen : A ← B
    Seen a b = P a b ⊎ Q a b
    Fresh : A ← B
    Fresh a b = (R ∘ Q) a b × (Seen a b → ⊥)
    module Col b = Round (λ x → P x b) (λ x → Q x b) (λ x → test x b)
    -- Composition stores the R edge first. The column proof stores
    -- membership in Q first, so transport fresh seeds in both ways.
    change : ∀ {P′ X Y : A → Set} → (∀ {x} → X x → Y x) → ∀ {a} → Grow P′ X a → Grow P′ Y a
    change f (seed q) = seed (f q)
    change f (step p e avoid) = step (change f p) e avoid
    forward : θ P Q ⊆ θ Seen Fresh
    forward {a} {b} t with Col.forward b t
    ... | inl s = inl s
    ... | inr g = inr (change (λ { ((x , q , r) , no) → (x , r , q) , no }) g)
    backward : θ Seen Fresh ⊆ θ P Q
    backward {a} {b} (inl s) = Col.backward b (inl s)
    backward {a} {b} (inr g) = Col.backward b (inr (change (λ { ((x , r , q) , no) → (x , q , r) , no }) g))
