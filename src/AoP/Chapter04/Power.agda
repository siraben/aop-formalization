{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.Power where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id; graph)
private variable A B C : Set

-- §4.6. A power object lives one universe above its elements. Membership
-- is application; equality of subsets means inclusion in both directions.
ℙ : Set → Set₁
ℙ A = A → Set

infix 4 _∈_ _≐_
_∈_ : A → ℙ A → Set
a ∈ X = X a

_≐_ : ℙ A → ℙ A → Set
X ≐ Y = (∀ a → a ∈ X → a ∈ Y) × (∀ a → a ∈ Y → a ∈ X)

Λ : (B ← A) → A → ℙ B
Λ R a b = R b a

-- Cancellation and reflection: transposing a relation changes only the
-- order in which the input and a candidate output are supplied.
cancel-Λ : (R : B ← A) → ∀ a b → (b ∈ Λ R a) ≡ R b a
cancel-Λ R a b = refl

reflect-Λ : (X : ℙ A) → (λ a → a ∈ X) ≐ X
reflect-Λ X = (λ _ x → x) , (λ _ x → x)

fusion-Λ : (R : C ← B) (f : A → B) → ∀ a → Λ (R ∘ graph f) a ≐ Λ R (f a)
fusion-Λ R f a = (λ { c (_ , r , refl) → r }) , (λ c r → _ , r , refl)

-- Existential image: keep an output if *some* admissible input produces it.
ℰ : (B ← A) → ℙ A → ℙ B
ℰ {A = A} R X b = Σ A λ a → R b a × X a

absorption : (S : C ← B) (R : B ← A) → ∀ a → ℰ S (Λ R a) ≐ Λ (S ∘ R) a
absorption S R a = (λ _ p → p) , (λ _ p → p)

image-id : (X : ℙ A) → ℰ Id X ≐ X
image-id X = (λ { _ (_ , refl , x) → x }) , (λ a x → a , refl , x)

image-comp : (S : C ← B) (R : B ← A) (X : ℙ A) → ℰ (S ∘ R) X ≐ ℰ S (ℰ R X)
image-comp S R X = (λ { _ (a , (b , s , r) , x) → b , s , a , r , x }) ,
                   (λ { _ (b , s , a , r , x) → a , (b , s , r) , x })
