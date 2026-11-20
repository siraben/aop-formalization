{-# OPTIONS --safe --without-K #-}
module AoP.PartialEquivalence where

open import AoP.Prelude
open import AoP.Relations

-- Exercises 4.13–14 in Rel. Symmetry and transitivity give a loop at
-- the source of each edge, even if isolated points have no loops. This
-- supplies the intermediate point for the reverse inclusion in idempotence.
module Laws {A : Set} (R : A ← A) where
  Sym = R ⊆ R ˘
  Trans = R ∘ R ⊆ R

  expand : Sym → Trans → R ⊆ R ∘ R
  expand sym tr {b} {a} r = a , r , tr (b , sym r , r)

  -- R ∘ R˘ relates two outputs when they share an input. A common
  -- input can always be read in either order, giving the converse.
  forward : Sym → Trans → (R ⊆ R ∘ R ˘) × (R ∘ R ˘ ⊆ R)
  forward sym tr = (λ r → let a , p , q = expand sym tr r in a , p , sym q) ,
                   (λ { (a , p , q) → tr (a , p , sym q) })

  reverse : (R ⊆ R ∘ R ˘) → (R ∘ R ˘ ⊆ R) → Sym × Trans
  reverse into out = sym , λ { (x , p , q) → out (x , p , sym q) }
    where sym : Sym
          sym r with into r
          ... | a , p , q = out (a , q , p)
