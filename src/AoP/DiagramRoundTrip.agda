{-# OPTIONS --safe --without-K #-}
module AoP.DiagramRoundTrip where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.WalkingArrow
open import AoP.DiagramEvaluation using (module Evaluate)
open import AoP.ArrowDiagram using (module Canonical)

-- Exercise 2.19. Rebuilding an arbitrary diagram from its generating
-- arrow keeps both endpoints and that arrow. The old diagram may carry
-- different identity-law proofs. Compare diagrams by an isomorphism
-- whose components at both endpoints are identities.
module Round {o h e} (C : Category o h e) where
  open Category C
  open Evaluate C
  open Canonical C using (canonical)
  open Functor using (F₀; F₁)
  open Natural using (η)

  rebuild : Category.Obj Diag → Category.Obj Diag
  rebuild F = F₀ canonical (F₀ evaluate F)

  module At (F : Category.Obj Diag) where
    module Out = Diagrams.Maps C (rebuild F) F
    module In = Diagrams.Maps C F (rebuild F)

    across : F₁ F go ∘ identity ≈ identity ∘ F₁ F go
    across = transitive (unitʳ _) (symmetric (unitˡ _))

    out : Natural (rebuild F) F
    out = Out.write (Out.box identity identity across)
    into : Natural F (rebuild F)
    into = In.write (In.box identity identity across)

    old-round : ∀ x → η out x ∘ η into x ≈ identity
    old-round src = unitˡ _
    old-round dst = unitˡ _
    new-round : ∀ x → η into x ∘ η out x ≈ identity
    new-round src = unitˡ _
    new-round dst = unitˡ _

  -- The comparison itself commutes with transformations of diagrams:
  -- at each endpoint the two sides insert identity on opposite sides.
  natural : ∀ {F G : Category.Obj Diag} (α : Natural F G) x →
            η α x ∘ η (At.out F) x ≈ η (At.out G) x ∘ η (F₁ canonical (F₁ evaluate α)) x
  natural α src = transitive (unitʳ _) (symmetric (unitˡ _))
  natural α dst = transitive (unitʳ _) (symmetric (unitˡ _))
