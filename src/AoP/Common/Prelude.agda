{-# OPTIONS --safe --without-K #-}
module AoP.Common.Prelude where

open import Agda.Builtin.Equality public
open import Agda.Builtin.List public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Unit public

infixr 4 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

cong : ∀ {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

infixr 2 _∙_
_∙_ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ∙ q = q

-- Read a calculation down the left margin. The hint between angle brackets
-- justifies this step only; empty brackets indicate computation by definition.
infix  1 begin_
infixr 2 _≡⟨_⟩_ _≡⟨⟩_
infix  3 _∎
begin_ : ∀ {A : Set} {x y : A} → x ≡ y → x ≡ y
begin p = p
_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q
_≡⟨⟩_ : ∀ {A : Set} (x : A) {y} → x ≡ y → x ≡ y
x ≡⟨⟩ p = p
_∎ : ∀ {A : Set} (x : A) → x ≡ x
x ∎ = refl

-- An optimization calculation may assume only transitivity. End with
-- the actual last inequality rather than demanding reflexivity there.
module BoundSteps {A : Set} (_≤_ : A → A → Set)
                  (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z) where
  infixr 2 _≤⟨_⟩_
  _≤⟨_⟩_ : (x : A) → ∀ {y z} → x ≤ y → y ≤ z → x ≤ z
  _ ≤⟨ xy ⟩ yz = trans xy yz
  infix 3 last-step
  last-step : (x y : A) → x ≤ y → x ≤ y
  last-step x y xy = xy
  syntax last-step x y xy = x ≤⟨ xy ⟩∎ y
