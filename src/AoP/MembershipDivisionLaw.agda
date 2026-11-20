{-# OPTIONS --safe --without-K #-}
module AoP.MembershipDivisionLaw where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.LeftDivision using (_＼_)
open import AoP.Shunting using (Id)

-- Exercise 6.18: use the identity-column law twice. First expand
-- member ＼ S through L S, then combine the two lifted arrows and
-- contract the identity-column law at R ∘ S.
module Law (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (join : ∀ {A B C} (R : C ← B) (S : B ← A) → L R ∘ L S ⊆ L (R ∘ S))
  (split : ∀ {A B C} (R : C ← B) (S : B ← A) → L (R ∘ S) ⊆ L R ∘ L S)
  (member : ∀ A → A ← F A) where
  Columns : ∀ {A B} → B ← A → F B ← A
  Columns {B = B} R = member B ＼ R
  record IdentityLaw : Set₁ where
    field
      contract : ∀ {A B} (R : B ← A) → L R ∘ Columns Id ⊆ Columns R
      expand : ∀ {A B} (R : B ← A) → Columns R ⊆ L R ∘ Columns Id
  record CompositeLaw : Set₁ where
    field
      contract : ∀ {A B C} (R : C ← B) (S : B ← A) → L R ∘ Columns S ⊆ Columns (R ∘ S)
      expand : ∀ {A B C} (R : C ← B) (S : B ← A) → Columns (R ∘ S) ⊆ L R ∘ Columns S
  generalize : IdentityLaw → CompositeLaw
  CompositeLaw.contract (generalize law) R S (b , r , cs) with IdentityLaw.expand law S cs
  ... | a , s , one = IdentityLaw.contract law (R ∘ S) (a , join R S (b , r , s) , one)
  CompositeLaw.expand (generalize law) R S cs with IdentityLaw.expand law (R ∘ S) cs
  ... | a , rs , one with split R S rs
  ... | b , r , s = b , r , IdentityLaw.contract law S (a , s , one)

  -- Specialize S to Id. Discharge the remaining unit inside the
  -- residual pointwise, without requiring equality of relations.
  specialize : CompositeLaw → IdentityLaw
  IdentityLaw.contract (specialize law) R w m with CompositeLaw.contract law R Id w m
  ... | _ , r , refl = r
  IdentityLaw.expand (specialize law) R cs = CompositeLaw.expand law R Id (λ m → _ , cs m , refl)
