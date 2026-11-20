{-# OPTIONS --safe --without-K #-}
module AoP.EditDropCalculation where

open import AoP.Prelude
open import AoP.EditScript
open import AoP.EditSuffix using (module Target)
open import AoP.EditDropSquares using (module Squares)
open import AoP.ScriptRelationInduction using (module Law)
open import AoP.Relations using (_∘_; _⊆_)
open import AoP.NatOrder using (rid; s≤; weaken)

-- Exercise 9.7. Use constructor-graph induction on the inclusion,
-- with each decoder square supplying the middle endpoint. The only
-- recursive obligation is exposed by commuting Drop past deletion.
module Calculation {A : Set} where
  open Scripts {A} using (edit; step)
  open Target {A} using (Drop; E; R)
  open Squares {A}
  module I = Law (Drop ∘ E) (E ∘ R)
  base : (Drop ∘ E) ∘ I.Empty ⊆ (E ∘ R) ∘ I.Empty
  base (.[] , (_ , () , refl) , refl)
  cons : ∀ op es → I.Local es → ∀ {p} → ((Drop ∘ E) ∘ I.Push op) p es → ((E ∘ R) ∘ I.Push op) p es
  cons (insert a) es ih (_ , (_ , d , refl) , refl) with insert-square a {a = edit es} (_ , d , refl)
  ... | refl = _ , (es , refl , weaken (rid _)) , refl
  cons (copy a) es ih (_ , (_ , d , refl) , refl) with copy-square a {a = edit es} (_ , d , refl)
  ... | refl = _ , ((delete a ∷ es) , refl , rid _) , refl
  cons (delete a) es ih (_ , (_ , d , refl) , refl) with delete-square a {a = edit es} (_ , d , refl)
  ... | mid , refl , next with ih (edit es , next , refl)
  ...   | shorter , eq , bound = _ , ((delete a ∷ shorter) , cong (step (delete a)) eq , s≤ bound) , refl

  inclusion : Drop ∘ E ⊆ E ∘ R
  inclusion = I.derive base cons
