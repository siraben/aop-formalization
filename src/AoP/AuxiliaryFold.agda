{-# OPTIONS --safe --without-K #-}
module AoP.AuxiliaryFold where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)

-- Exercise 3.4. Suppose the desired answer for a parent can be read
-- from each child's answer and an auxiliary fold on that child. Store
-- both in the fold carrier. The auxiliary update ignores the answers;
-- the main update may use both. Fold uniqueness proves the invariant.
module Derive (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Functor F using (F₀; F₁; composition; resp)
  open Theory.Initial I
  module Cache {A B : Set} (h : F₀ B → B) (f : μ → A) (g : F₀ (A × B) → A)
               (step : ∀ t → f (inn t) ≡ g (F₁ (λ x → f x , ⦅ h ⦆ x) t)) where
    both : μ → A × B
    both x = f x , ⦅ h ⦆ x

    k : F₀ (A × B) → A × B
    k t = g t , h (F₁ snd t)

    private
      auxiliary : ∀ t → ⦅ h ⦆ (inn t) ≡ h (F₁ snd (F₁ both t))
      auxiliary t = begin
        ⦅ h ⦆ (inn t) ≡⟨ computation h t ⟩
        h (F₁ ⦅ h ⦆ t) ≡⟨ cong h (composition snd both t) ⟩
        h (F₁ snd (F₁ both t)) ∎

      square : Theory.Hom F inn k both
      square t = begin
        both (inn t) ≡⟨ cong (λ a → a , ⦅ h ⦆ (inn t)) (step t) ⟩
        (g (F₁ both t) , ⦅ h ⦆ (inn t)) ≡⟨ cong (g (F₁ both t) ,_) (auxiliary t) ⟩
        k (F₁ both t) ∎

    invariant : ∀ x → both x ≡ ⦅ k ⦆ x
    invariant = unique k both square

    answer : ∀ x → f x ≡ fst (⦅ k ⦆ x)
    answer x = cong fst (invariant x)
