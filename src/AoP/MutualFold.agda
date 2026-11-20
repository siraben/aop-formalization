{-# OPTIONS --safe --without-K #-}
module AoP.MutualFold where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)

-- Exercise 3.8. Each child returns two values. Either parent update may
-- inspect both. The two recurrence equations characterize a *single*
-- fold into a pair, in both directions, without function extensionality.
module Theorem (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Functor F using (F₀; F₁; resp; composition)
  open Theory.Initial I
  module Pair {A B : Set} (f : μ → A) (g : μ → B)
              (h : F₀ (A × B) → A) (k : F₀ (A × B) → B) where
    fg : μ → A × B
    fg x = f x , g x
    hk : F₀ (A × B) → A × B
    hk t = h t , k t
    Equations = (∀ t → f (inn t) ≡ h (F₁ fg t)) × (∀ t → g (inn t) ≡ k (F₁ fg t))
    Solution = ∀ x → fg x ≡ ⦅ hk ⦆ x

    combine : Equations → Solution
    combine (first , second) = unique hk fg λ t → begin
      fg (inn t) ≡⟨ cong (λ a → a , g (inn t)) (first t) ⟩
      (h (F₁ fg t) , g (inn t)) ≡⟨ cong (h (F₁ fg t) ,_) (second t) ⟩
      hk (F₁ fg t) ∎

    separate : Solution → Equations
    separate law = (λ t → cong fst (both t)) , (λ t → cong snd (both t))
      where
      back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
      back refl = refl
      both : ∀ t → fg (inn t) ≡ hk (F₁ fg t)
      both t = begin
        fg (inn t) ≡⟨ law (inn t) ⟩
        ⦅ hk ⦆ (inn t) ≡⟨ computation hk t ⟩
        hk (F₁ ⦅ hk ⦆ t) ≡⟨ cong hk (resp (λ x → back (law x)) t) ⟩
        hk (F₁ fg t) ∎

  -- Independent updates give banana-split. When the first update uses
  -- both results and only the second is independent, this is ex. 3.4.
  module Auxiliary {A B : Set} (f : μ → A) (b : F₀ B → B) (a : F₀ (A × B) → A) where
    module P = Pair f ⦅ b ⦆ a (λ t → b (F₁ snd t))
    derive : (∀ t → f (inn t) ≡ a (F₁ P.fg t)) → P.Solution
    derive eq = P.combine (eq , λ t → computation b t ∙ cong b (composition snd P.fg t))

  split : ∀ {A B : Set} (a : F₀ A → A) (b : F₀ B → B) →
          Pair.Solution ⦅ a ⦆ ⦅ b ⦆ (λ t → a (F₁ fst t)) (λ t → b (F₁ snd t))
  split a b = Auxiliary.derive ⦅ a ⦆ b _ (λ t → computation a t ∙ cong a (composition fst (λ x → ⦅ a ⦆ x , ⦅ b ⦆ x) t))
