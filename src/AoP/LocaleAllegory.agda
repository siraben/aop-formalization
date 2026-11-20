{-# OPTIONS --safe --without-K #-}
module AoP.LocaleAllegory where

open import AoP.Prelude
open import AoP.Categories using (Category)
open import AoP.ProductAllegory using (Laws)
open import AoP.LocaleRelations using (Frame; module Rel)
import AoP.LocaleIdentity as Identity
import AoP.LocaleComposition as Composition

-- Exercise 4.18. Use pointwise mutual inclusion as hom equality.
-- In particular, no equality test on the intermediate object is needed.
module Build (F : Frame) where
  open Frame F
  open Rel F
  open Identity.Law F
  open Composition.Law F
  comp-mono : ∀ {A B C} {g g′ : Rel C B} {f f′ : Rel B A} → g ⊆ g′ → f ⊆ f′ → (g ∘ f) ⊆ (g′ ∘ f′)
  comp-mono {g = g} {g′} {f} {f′} p q c a = least _ λ b → chain
    (pair (chain (left (g c b) (f b a)) (p c b)) (chain (right (g c b) (f b a)) (q b a))) (inject _ b)

  cat : Category _ _ _
  Category.Obj cat = Set
  Category.Hom cat A B = Rel B A
  Category._≈_ cat R S = (R ⊆ S) × (S ⊆ R)
  Category.identity cat = diag
  Category._∘_ cat = _∘_
  Category.reflexive cat = (λ _ _ → rid _) , (λ _ _ → rid _)
  Category.symmetric cat (p , q) = q , p
  Category.transitive cat (p , q) (s , t) = (λ b a → chain (p b a) (s b a)) , (λ b a → chain (t b a) (q b a))
  Category.compose-cong cat (p , q) (s , t) = comp-mono p s , comp-mono q t
  Category.unitˡ cat R = left-out R , left-in R
  Category.unitʳ cat R = right-out R , right-in R
  Category.assoc cat T S R = assoc-in T S R , assoc-out T S R

  algebra : Laws cat _
  Laws._⊑_ algebra = _⊆_
  Laws.respect algebra = fst
  Laws.trans algebra p q b a = chain (p b a) (q b a)
  Laws.antisym algebra p q = p , q
  Laws.meet algebra = _⊓_
  Laws.lower₁ algebra R S b a = left _ _
  Laws.lower₂ algebra R S b a = right _ _
  Laws.glb algebra p q b a = pair (p b a) (q b a)
  Laws.rev algebra = rev
  Laws.invol algebra R = (λ _ _ → rid _) , (λ _ _ → rid _)
  Laws.flip algebra S R = (λ a c → least _ λ b → chain (swap (S c b) (R b a)) (inject _ b)) ,
                         (λ a c → least _ λ b → chain (swap (R b a) (S c b)) (inject _ b))
  Laws.rev-mono algebra p a b = p b a
  Laws.mono algebra = comp-mono
  Laws.modular algebra = modular
