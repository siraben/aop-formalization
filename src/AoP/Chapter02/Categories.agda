{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.Categories where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import AoP.Common.Prelude

-- §2.1. Equality belongs to the hom-set: for functions this lets us use
-- pointwise equality, without assuming function extensionality.
record Category (o h e : Level) : Set (lsuc (o ⊔ h ⊔ e)) where
  infixr 8 _∘_
  infix  4 _≈_
  field
    Obj : Set o
    Hom : Obj → Obj → Set h
    _≈_ : ∀ {A B} → Hom A B → Hom A B → Set e
    identity : ∀ {A} → Hom A A
    _∘_ : ∀ {A B C} → Hom B C → Hom A B → Hom A C
    reflexive : ∀ {A B} {f : Hom A B} → f ≈ f
    symmetric : ∀ {A B} {f g : Hom A B} → f ≈ g → g ≈ f
    transitive : ∀ {A B} {f g k : Hom A B} → f ≈ g → g ≈ k → f ≈ k
    compose-cong : ∀ {A B C} {f g : Hom A B} {s t : Hom B C} →
                   s ≈ t → f ≈ g → s ∘ f ≈ t ∘ g
    unitˡ : ∀ {A B} (f : Hom A B) → identity ∘ f ≈ f
    unitʳ : ∀ {A B} (f : Hom A B) → f ∘ identity ≈ f
    assoc : ∀ {A B C D} (t : Hom C D) (s : Hom B C) (r : Hom A B) →
            (t ∘ s) ∘ r ≈ t ∘ (s ∘ r)

open import Agda.Primitive using (lzero)
Fun : Category (lsuc lzero) lzero lzero
Fun = record
  { Obj = Set; Hom = λ A B → A → B
  ; _≈_ = λ f g → ∀ x → f x ≡ g x
  ; identity = λ x → x; _∘_ = λ g f x → g (f x)
  ; reflexive = λ x → refl; symmetric = λ eq x → sym (eq x)
  ; transitive = λ p q x → p x ∙ q x
  ; compose-cong = compose; unitˡ = λ f x → refl; unitʳ = λ f x → refl
  ; assoc = λ t s r x → refl }
  where
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
  compose : ∀ {A B C : Set} {s t : B → C} {f g : A → B} →
            (∀ y → s y ≡ t y) → (∀ x → f x ≡ g x) → ∀ x → s (f x) ≡ t (g x)
  compose {s = s} {t} {f} {g} p q x = begin
    s (f x) ≡⟨ p (f x) ⟩
    t (f x) ≡⟨ cong t (q x) ⟩
    t (g x) ∎
