{-# OPTIONS --safe --without-K #-}
module AoP.SpanProduct where

open import Agda.Primitive using (_⊔_)
open import AoP.Categories
open import AoP.UniversalObjects using (module Universal)

-- §2.5. Fix the endpoints; the source of the two legs can vary. A
-- map of spans must preserve both observations. Equality compares the
-- underlying arrows, so the proofs that the triangles commute are hidden.
module Over {o h e} (C : Category o h e) (A B : Category.Obj C) where
  open Category C
  record Span : Set (o ⊔ h) where
    constructor span
    field apex : Obj
          left : Hom apex A
          right : Hom apex B
  open Span
  record Map (S T : Span) : Set (h ⊔ e) where
    constructor via
    field arrow : Hom (apex S) (apex T)
          l : left T ∘ arrow ≈ left S
          r : right T ∘ arrow ≈ right S
  open Map
  private
    paste : ∀ {I J K L} {p : Hom K L} {q : Hom J L} {r : Hom I L}
              {f : Hom J K} {g : Hom I J} → p ∘ f ≈ q → q ∘ g ≈ r → p ∘ (f ∘ g) ≈ r
    paste u v = transitive (symmetric (assoc _ _ _)) (transitive (compose-cong u reflexive) v)
  spans : Category _ _ _
  Category.Obj spans = Span
  Category.Hom spans = Map
  Category._≈_ spans f g = arrow f ≈ arrow g
  Category.identity spans = via identity (unitʳ _) (unitʳ _)
  Category._∘_ spans f g = via (arrow f ∘ arrow g) (paste (l f) (l g)) (paste (r f) (r g))
  Category.reflexive spans = reflexive
  Category.symmetric spans = symmetric
  Category.transitive spans = transitive
  Category.compose-cong spans = compose-cong
  Category.unitˡ spans f = unitˡ (arrow f)
  Category.unitʳ spans f = unitʳ (arrow f)
  Category.assoc spans f g k = assoc (arrow f) (arrow g) (arrow k)

  module U = Universal spans
  -- A terminal map out of (f,g) computes the pairing. Its two triangle
  -- proofs are cancellation; its uniqueness is pairing uniqueness.
  module Pair {T} (t : U.Terminal T) where
    pair : ∀ {X} → Hom X A → Hom X B → Hom X (apex T)
    pair f g = arrow (U.Terminal.enter t (span _ f g))
    cancel-left : ∀ {X} (f : Hom X A) g → left T ∘ pair f g ≈ f
    cancel-left f g = l (U.Terminal.enter t _)
    cancel-right : ∀ {X} f (g : Hom X B) → right T ∘ pair f g ≈ g
    cancel-right f g = r (U.Terminal.enter t _)
    unique : ∀ {X} (f : Hom X A) g (m : Hom X (apex T)) → left T ∘ m ≈ f → right T ∘ m ≈ g → m ≈ pair f g
    unique f g m u v = U.Terminal.unique t (via m u v)

  -- Conversely, the ordinary product laws construct the terminal span.
  terminal : ∀ T (pair : ∀ {X} → Hom X A → Hom X B → Hom X (apex T)) →
    (∀ {X} (f : Hom X A) g → left T ∘ pair f g ≈ f) →
    (∀ {X} f (g : Hom X B) → right T ∘ pair f g ≈ g) →
    (∀ {X} (f : Hom X A) g (m : Hom X (apex T)) → left T ∘ m ≈ f → right T ∘ m ≈ g → m ≈ pair f g) → U.Terminal T
  U.Terminal.enter (terminal T pair pl pr un) S = via (pair (left S) (right S)) (pl _ _) (pr _ _)
  U.Terminal.unique (terminal T pair pl pr un) m = un _ _ (arrow m) (l m) (r m)
