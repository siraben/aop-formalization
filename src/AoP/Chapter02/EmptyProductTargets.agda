{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.EmptyProductTargets where

open import AoP.Common.Prelude
open import AoP.Chapter02.EmptyTargets using (InitialSource; Invertible)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 2.21. In Fun × Fun the initial pair has BOTH components
-- empty. Test either target component separately: send Bool there
-- constantly and use the empty type for the other source component.
EmptyPair : Set → Set → Set₁
EmptyPair A B = (X Y : Set) (f : X → A) (g : Y → B) →
  (InitialSource X × InitialSource Y) ⊎ (Invertible f × Invertible g)

from-empty : ∀ {A B} → InitialSource A × InitialSource B → EmptyPair A B
from-empty (a , b) X Y f g = inl ((λ x → a (f x)) , (λ y → b (g y)))

private
  never : ∀ {A : Set} → ⊥ → A
  never ()
  clash : ∀ {x : Bool} → x ≡ true → x ≡ false → ⊥
  clash refl ()
  constant : ∀ {A : Set} (a : A) → Invertible (λ (_ : Bool) → a) → ⊥
  constant a (g , law , _) = clash (law true) (law false)

to-empty : ∀ {A B} → EmptyPair A B → InitialSource A × InitialSource B
to-empty {A} {B} e = left , right
  where left : InitialSource A
        left a with e Bool ⊥ (λ _ → a) never
        ... | inl (x , _) = x true
        ... | inr (inv , _) = constant a inv
        right : InitialSource B
        right b with e ⊥ Bool never (λ _ → b)
        ... | inl (_ , y) = y true
        ... | inr (_ , inv) = constant b inv
