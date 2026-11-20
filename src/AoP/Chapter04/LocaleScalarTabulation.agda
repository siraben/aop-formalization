{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.LocaleScalarTabulation where

open import AoP.Common.Prelude
open import AoP.Chapter04.LocaleRelations using (Frame; module Rel)
import AoP.Chapter04.LocaleIdentity as Identity

-- Exercise 4.25. Every total leg into a singleton has grade top at
-- every input. Consequently a scalar tabulated by two such legs must
-- be equivalent to a join of copies of top indexed by its witnesses.
module Law (F : Frame) where
  open Frame F
  open Rel F
  open Identity.Law F using (top; above; diag)
  Total : ∀ {X} → Rel ⊤ X → Set
  Total f = diag ⊆ (rev f ∘ f)
  full : ∀ {X} (f : Rel ⊤ X) → Total f → ∀ x → top ≤ f tt x
  full f total x = chain (inject (λ (_ : x ≡ x) → top) refl)
    (chain (total x x) (least _ λ { tt → left (f tt x) (f tt x) }))

  support : (X : Set) → V
  support X = join {X} (λ _ → top)
  necessary : ∀ {X} (f g : Rel ⊤ X) → Total f → Total g →
              let v = (g ∘ rev f) tt tt in (v ≤ support X) × (support X ≤ v)
  necessary {X} f g tf tg =
    least _ (λ x → chain (above _) (inject (λ (_ : X) → top) x)) ,
    least (λ (_ : X) → top) (λ x → chain (pair (full g tg x) (full f tf x)) (inject _ x))
