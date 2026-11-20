{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ModularDisjointness where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §4.5: rotate a disjointness test across the first step of a path.
-- No complement is needed here. The modular law places the overlap
-- inside a composite; if that overlap is empty the path is empty too.
module Rotate {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  module Zero (zero : ∀ {A B} → Hom A B)
    (annihilate : ∀ {A B D} (f : Hom B D) → (f ∘ zero {A} {B}) ⊑ zero) where
    private
      id≤ : ∀ {A B} {f : Hom A B} → f ⊑ f
      id≤ = respect reflexive
    swap : ∀ {A B} (f g : Hom A B) → meet f g ⊑ meet g f
    swap f g = glb (lower₂ f g) (lower₁ f g)
    contract : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
      meet s (rev r ∘ t) ⊑ zero → meet (r ∘ s) t ⊑ zero
    contract r s t disjoint = trans (modular r s t) (trans (mono id≤ disjoint) (annihilate r))
    expand : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
      meet (r ∘ s) t ⊑ zero → meet (rev r ∘ t) s ⊑ zero
    expand r s t disjoint = contract (rev r) t s (trans (glb (lower₁ _ _)
      (trans (lower₂ _ _) (mono (respect (invol r)) id≤))) (trans (swap t _) disjoint))

    -- The Boolean step is separate: complement converts a disjointness
    -- test into an inclusion. Double negation is needed only on t for
    -- the converse direction of this Schröder equivalence.
    module Complement (neg : ∀ {A B} → Hom A B → Hom A B)
      (intro : ∀ {A B} (x y : Hom A B) → meet x y ⊑ zero → x ⊑ neg y)
      (elim : ∀ {A B} (x y : Hom A B) → x ⊑ neg y → meet x y ⊑ zero) where
      forward : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
        (r ∘ s) ⊑ t → (rev r ∘ neg t) ⊑ neg s
      forward r s t path = intro _ _ (expand r s (neg t) (trans (glb (trans (lower₁ _ _) path) (lower₂ _ _))
        (trans (swap t (neg t)) (elim _ _ id≤))))
      backward : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
        neg (neg t) ⊑ t → (rev r ∘ neg t) ⊑ neg s → (r ∘ s) ⊑ t
      backward r s t stable stop = trans (intro _ _ (contract r s (neg t)
        (trans (swap s _) (elim _ _ stop)))) stable
