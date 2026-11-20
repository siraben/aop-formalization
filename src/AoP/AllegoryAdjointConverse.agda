{-# OPTIONS --safe --without-K #-}
module AoP.AllegoryAdjointConverse where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)
open import AoP.AllegoryMapComposition using () renaming (module Law to Maps)

-- Proposition 4.1, used by Lemma 5.1: an arrow with a right adjoint
-- is a map, and its adjoint has to be its converse. No elements or
-- tabulations enter the proof: the modular law does the essential work.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  open Maps L using (reverse-id; Map)
  private
    rid : ∀ {A B} {f : Hom A B} → f ⊑ f
    rid = respect reflexive
  module Pair {A B} (r : Hom A B) (s : Hom B A)
    (unit : identity ⊑ (s ∘ r)) (counit : (r ∘ s) ⊑ identity) where
    -- Intersect r with s˘. Modularity keeps enough of this restricted
    -- arrow to witness the unit, so the counit recovers all of r.
    part = meet r (rev s ∘ identity)
    witness : identity ⊑ (s ∘ part)
    witness = trans (glb unit rid) (modular s r identity)
    below : r ⊑ rev s
    below = trans (respect (symmetric (unitʳ r))) (trans (mono rid witness)
      (trans (respect (symmetric (assoc r s part))) (trans (mono counit rid)
      (trans (respect (unitˡ part)) (trans (lower₂ _ _) (respect (unitʳ _)))))))
  module Result {A B} (r : Hom A B) (s : Hom B A)
    (u : identity ⊑ (s ∘ r)) (c : (r ∘ s) ⊑ identity) where
    module Forward = Pair r s u c
    module Back = Pair (rev s) (rev r)
      (trans (respect (symmetric reverse-id)) (trans (rev-mono u) (respect (flip s r))))
      (trans (respect (symmetric (flip r s))) (trans (rev-mono c) (respect reverse-id)))
    agreed : s ≈ rev r
    agreed = antisym (trans (respect (symmetric (invol s))) (rev-mono (trans Back.below (respect (invol r)))))
      (trans (rev-mono Forward.below) (respect (invol s)))
    functional : Map r
    Map.entire functional = trans u (mono (respect agreed) rid)
    Map.simple functional = trans (mono rid (respect (symmetric agreed))) c
