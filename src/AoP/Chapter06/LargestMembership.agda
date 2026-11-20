{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.LargestMembership where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter06.MembershipDivisionLaw using (module Law)

-- Exercise 6.19. First restrict a competing selector to structures
-- whose members all equal the input. The resulting endotransformation
-- of identity is bounded by identity. Then expand an arbitrary
-- structure along its own membership column to remove the restriction.
module Largest (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (join : ∀ {A B C} (R : C ← B) (S : B ← A) → L R ∘ L S ⊆ L (R ∘ S))
  (split : ∀ {A B C} (R : C ← B) (S : B ← A) → L (R ∘ S) ⊆ L R ∘ L S)
  (member : ∀ A → A ← F A) where
  open Law F L join split member
  EndLax : (∀ A → A ← A) → Set₁
  EndLax X = ∀ {A B} (R : B ← A) → X B ∘ R ⊆ R ∘ X A
  Selector = ∀ A → A ← F A
  Lax : Selector → Set₁
  Lax X = ∀ {A B} (R : B ← A) → X B ∘ L R ⊆ R ∘ X A
  module Proof (membership : IdentityLaw)
    (largest-id : ∀ X → EndLax X → ∀ A → X A ⊆ Id) where
    natural : Lax member
    natural {A} R (t , m , r) = CompositeLaw.contract (generalize membership) R (member A) (_ , r , (λ x → x)) m
    module Bound (X : Selector) (lax : Lax X) where
      endo : ∀ A → A ← A
      endo A = X A ∘ Columns Id
      restrict : EndLax endo
      restrict R (b , (t , x , one) , r) with IdentityLaw.expand membership R (λ m → substR (one m) r)
        where substR : ∀ {u v a} → u ≡ v → R v a → R u a
              substR refl p = p
      ... | s , lifted , single with lax R (t , x , lifted)
      ... | a , rel , chosen = a , rel , s , chosen , single
      maximum : ∀ A → X A ⊆ member A
      maximum A {a = t} pick with IdentityLaw.expand membership (member A) {b = t} {a = t} (λ m → m)
      ... | s , lifted , one with lax (member A) (t , pick , lifted)
      ... | u , belongs , selected with largest-id endo restrict (F A) (s , selected , one)
      ... | refl = belongs
