{-# OPTIONS --safe --without-K #-}
module AoP.RightModularDisjointness where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)
open import AoP.ModularDisjointness using (module Rotate)

-- Exercise 4.43. Turn the disjointness triangle around by taking
-- converses. A monotone involution preserves disjointness: a lower
-- bound of the two reversed arrows reverses to an original lower bound.
module Rule {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  module Proof (zero : ∀ {A B} → Hom A B)
    (bottom : ∀ {A B} (x : Hom A B) → zero ⊑ x)
    (annihilate : ∀ {A B D} (f : Hom B D) → (f ∘ zero {A} {B}) ⊑ zero) where
    module Z = Rotate.Zero L zero annihilate
    reverse-test : ∀ {A B} (x y : Hom A B) → meet x y ⊑ zero → meet (rev x) (rev y) ⊑ zero
    reverse-test x y disjoint = trans (respect (symmetric (invol m))) (trans (rev-mono inside) empty)
      where m = meet (rev x) (rev y)
            inside = trans (glb (trans (rev-mono (lower₁ _ _)) (respect (invol x)))
                                (trans (rev-mono (lower₂ _ _)) (respect (invol y)))) disjoint
            empty = trans (rev-mono (bottom (rev zero))) (respect (invol zero))
    -- Move a known disjointness bound down along two inclusions.
    narrow : ∀ {A B} {x y u v : Hom A B} → x ⊑ u → y ⊑ v → meet u v ⊑ zero → meet x y ⊑ zero
    narrow a b stop = trans (glb (trans (lower₁ _ _) a) (trans (lower₂ _ _) b)) stop
    reversed-path : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
      meet (r ∘ s) t ⊑ zero → meet (rev s ∘ rev r) (rev t) ⊑ zero
    reversed-path r s t stop = narrow (respect (symmetric (flip r s))) (respect reflexive) (reverse-test _ _ stop)

    -- Apply the left rotation to the reversed triangle. Involution
    -- then restores its labels; the overlap now tests the other factor.
    rotate : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
      meet (r ∘ s) t ⊑ zero → meet (t ∘ rev s) r ⊑ zero
    rotate r s t stop = narrow (trans (respect (symmetric (invol _))) (rev-mono (respect (flip t (rev s)))))
      (respect (symmetric (invol r))) (reverse-test _ _ (Z.expand (rev s) (rev r) (rev t) (reversed-path r s t stop)))

    module Complement (neg : ∀ {A B} → Hom A B → Hom A B)
      (intro : ∀ {A B} (x y : Hom A B) → meet x y ⊑ zero → x ⊑ neg y)
      (elim : ∀ {A B} (x y : Hom A B) → x ⊑ neg y → meet x y ⊑ zero) where
      forward : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
        (r ∘ s) ⊑ t → (neg t ∘ rev s) ⊑ neg r
      forward r s t path = intro _ _ (rotate r s (neg t)
        (narrow path (respect reflexive) (trans (Z.swap t _) (elim _ _ (respect reflexive)))))

      -- Rotate again with s reversed. The restored path lies below
      -- double negation of its target, so stability finishes the proof.
      backward : ∀ {A B D} (r : Hom B D) (s : Hom A B) (t : Hom A D) →
        neg (neg t) ⊑ t → (neg t ∘ rev s) ⊑ neg r → (r ∘ s) ⊑ t
      backward r s t stable stop = trans (intro _ _ (narrow
        (mono (respect reflexive) (respect (symmetric (invol s)))) (respect reflexive)
        (rotate (neg t) (rev s) r (elim _ _ stop)))) stable
