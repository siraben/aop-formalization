{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ParameterRecursion where

open import AoP.Common.Prelude

-- Exercise 3.41, for container trees. Each output position is routed
-- to one immediate child, with a new parameter. The output layer may
-- rearrange, repeat, or omit children. Thus the parameter need not
-- decrease: stripping the input constructor supplies the induction.
module Law (S : Set) (Pos : S → Set) (T : Set) (Slot : T → Set)
           (P : Set) (shape : P → S → T)
           (route : ∀ p s → Slot (shape p s) → P × Pos s) where
  data Tree : Set where
    node : (s : S) → (Pos s → Tree) → Tree

  module Solve {B : Set} (h : (t : T) → (Slot t → B) → B)
    (respect : ∀ t (f g : Slot t → B) → (∀ i → f i ≡ g i) → h t f ≡ h t g) where
    solve : P → Tree → B
    solve p (node s kids) = h (shape p s) λ i →
      solve (fst (route p s i)) (kids (snd (route p s i)))

    Equation : (P → Tree → B) → Set
    Equation f = ∀ p s kids → f p (node s kids) ≡ h (shape p s)
      (λ i → f (fst (route p s i)) (kids (snd (route p s i))))

    computes : Equation solve
    computes p s kids = refl

    unique : ∀ f → Equation f → ∀ p x → f p x ≡ solve p x
    unique f eq p (node s kids) = eq p s kids ∙ respect (shape p s) _ _
      (λ i → unique f eq (fst (route p s i)) (kids (snd (route p s i))))
