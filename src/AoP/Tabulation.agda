{-# OPTIONS --safe --without-K #-}
module AoP.Tabulation where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph)

-- §4.3. Store a row for each related pair. In the constructive model
-- membership carries evidence: distinct proofs can give distinct rows.
module Table {A B : Set} (R : B ← A) where
  record Row : Set where
    constructor row
    field
      target : B
      source : A
      member : R target source
  open Row public

  span : B ← A
  span = graph target ∘ graph source ˘

  -- Reading the two columns reconstructs exactly the original relation.
  factor : R ⊆ span
  factor {b} {a} r = row b a r , refl , refl

  reconstruct : span ⊆ R
  reconstruct (row b a r , refl , refl) = r

  -- No duplicate pairs when membership is a proposition. This premise
  -- is local to the table; we do not assume global proof irrelevance.
  joint-monic : (∀ b a (p q : R b a) → p ≡ q) →
                (x y : Row) → target x ≡ target y → source x ≡ source y → x ≡ y
  joint-monic prop (row b a p) (row .b .a q) refl refl = cong (row b a) (prop b a p q)

  -- The mediating map of a span is constructed a row at a time.
  mediate : ∀ {X : Set} (f : X → B) (g : X → A) →
            graph f ∘ graph g ˘ ⊆ R → X → Row
  mediate f g incl x = row (f x) (g x) (incl (x , refl , refl))

  unique : ∀ {X : Set} (prop : ∀ b a (p q : R b a) → p ≡ q)
           (h k : X → Row) → (∀ x → target (h x) ≡ target (k x)) →
           (∀ x → source (h x) ≡ source (k x)) → ∀ x → h x ≡ k x
  unique prop h k t s x = joint-monic prop (h x) (k x) (t x) (s x)
