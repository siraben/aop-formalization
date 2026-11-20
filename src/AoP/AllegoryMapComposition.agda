{-# OPTIONS --safe --without-K #-}
module AoP.AllegoryMapComposition where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)

-- §4.2. Compose maps without assuming closure of the class of maps.
-- A map is an arrow with a unit (entire) and a counit (simple).
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  record Map {A B} (f : Hom A B) : Set p where
    field entire : identity ⊑ (rev f ∘ f)
          simple : (f ∘ rev f) ⊑ identity
  open Map
  private
    rid : ∀ {A B} {f : Hom A B} → f ⊑ f
    rid = respect reflexive
    -- Expose a middle round trip so monotonicity can enlarge or
    -- contract it. All the rearrangements here are category laws.
    nest : ∀ {A B D E H} (d : Hom E H) (c : Hom D E) (b : Hom B D) (a : Hom A B) →
      ((d ∘ c) ∘ (b ∘ a)) ≈ (d ∘ ((c ∘ b) ∘ a))
    nest d c b a = transitive (assoc _ _ _) (compose-cong reflexive (symmetric (assoc _ _ _)))
  -- Reverse the trivial composite id ∘ rev id. On the left double
  -- converse gives id; on the right the reversal law leaves rev id.
  reverse-id : ∀ {A} → rev (identity {A}) ≈ identity
  reverse-id {A} = transitive (symmetric (unitˡ _))
    (transitive (compose-cong (symmetric (invol identity)) reflexive)
    (transitive (symmetric (flip identity (rev identity)))
    (transitive (antisym (rev-mono (respect (unitˡ _))) (rev-mono (respect (symmetric (unitˡ _))))) (invol identity))))
  id-map : ∀ {A} → Map (identity {A})
  entire id-map = respect (transitive (symmetric reverse-id) (symmetric (unitʳ _)))
  simple id-map = respect (transitive (unitˡ _) reverse-id)
  compose : ∀ {A B D} {g : Hom B D} {f : Hom A B} → Map g → Map f → Map (g ∘ f)
  entire (compose {g = g} {f} mg mf) = trans (entire mf) (trans
    (mono rid (trans (respect (symmetric (unitˡ f))) (mono (entire mg) rid)))
    (trans (respect (symmetric (nest (rev f) (rev g) g f))) (mono (respect (symmetric (flip g f))) rid)))
  simple (compose {g = g} {f} mg mf) = trans (mono rid (respect (flip g f)))
    (trans (respect (nest g f (rev f) (rev g))) (trans
    (mono rid (trans (mono (simple mf) rid) (respect (unitˡ (rev g))))) (simple mg)))
