{-# OPTIONS --safe --without-K #-}
module AoP.Functors where

open import Agda.Primitive using (_⊔_; lsuc)
open import AoP.Prelude
open import AoP.Categories
open import AoP.Horner using (map)

-- §2.2. An object map determines the endpoints of the arrow map.
-- The three obligations make that map well-defined on equivalent arrows
-- and ensure it respects the empty path and concatenation of paths.
record Functor {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′) :
               Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′)) where
  private module C = Category C
  private module D = Category D
  field
    F₀ : C.Obj → D.Obj
    F₁ : ∀ {A B} → C.Hom A B → D.Hom (F₀ A) (F₀ B)
    resp : ∀ {A B} {f g : C.Hom A B} → f C.≈ g → F₁ f D.≈ F₁ g
    identity : ∀ {A} → F₁ (C.identity {A}) D.≈ D.identity
    composition : ∀ {A B E} (g : C.Hom B E) (f : C.Hom A B) →
                  F₁ (g C.∘ f) D.≈ (F₁ g D.∘ F₁ f)

-- List is an endofunctor on Fun. These proofs compare functions on an
-- arbitrary input, so no equality of Agda functions is needed.
map-resp : ∀ {A B : Set} {f g : A → B} → (∀ x → f x ≡ g x) →
           ∀ xs → map f xs ≡ map g xs
map-resp p [] = refl
map-resp {f = f} {g} p (x ∷ xs) = begin
  f x ∷ map f xs ≡⟨ cong (_∷ map f xs) (p x) ⟩
  g x ∷ map f xs ≡⟨ cong (g x ∷_) (map-resp p xs) ⟩
  g x ∷ map g xs ∎

map-id : ∀ {A : Set} (xs : List A) → map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

map-comp : ∀ {A B C : Set} (g : B → C) (f : A → B) xs →
           map (λ x → g (f x)) xs ≡ map g (map f xs)
map-comp g f [] = refl
map-comp g f (x ∷ xs) = cong (g (f x) ∷_) (map-comp g f xs)

Lists : Functor Fun Fun
Lists = record { F₀ = List; F₁ = map; resp = map-resp
               ; identity = map-id; composition = map-comp }
