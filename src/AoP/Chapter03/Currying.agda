{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.Currying where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter01.Naturality using (_++_)
private variable A B C D : Set

-- §3.5. The exponential B ⇒ C in Fun is Agda's function type. State
-- its universal property pointwise on both arguments to avoid funext.
apply : (B → C) × B → C
apply (f , b) = f b

curry : (A × B → C) → A → B → C
curry f a b = f (a , b)

uncurry : (A → B → C) → A × B → C
uncurry g (a , b) = apply (g a , b)

unique→ : (g : A → B → C) (f : A × B → C) →
          (∀ a b → g a b ≡ curry f a b) → ∀ p → uncurry g p ≡ f p
unique→ g f k (a , b) = k a b

unique← : (g : A → B → C) (f : A × B → C) →
          (∀ p → uncurry g p ≡ f p) → ∀ a b → g a b ≡ curry f a b
unique← g f k a b = k (a , b)

-- The recursive result is a function awaiting the right-hand list.
ccat : List A → List A → List A
ccat = ⦅ (λ ys → ys) ∣ (λ a append ys → a ∷ append ys) ⦆

ccat-correct : (xs ys : List A) → ccat xs ys ≡ xs ++ ys
ccat-correct [] ys = refl
ccat-correct (x ∷ xs) ys = begin
  ccat (x ∷ xs) ys   ≡⟨⟩
  x ∷ ccat xs ys     ≡⟨ cong (x ∷_) (ccat-correct xs ys) ⟩
  (x ∷ xs) ++ ys ∎
