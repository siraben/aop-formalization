{-# OPTIONS --safe --without-K #-}
module AoP.Prelude where

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
