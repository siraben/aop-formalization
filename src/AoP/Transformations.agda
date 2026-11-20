{-# OPTIONS --safe --without-K #-}
module AoP.Transformations where

open import Agda.Primitive using (_⊔_; lsuc)
open import AoP.Categories
open import AoP.Functors
open import AoP.Naturality using (reverse; reverse-natural)

-- §2.3. Each object has a component arrow. Naturality says we can move
-- that component across any arrow f by changing its object index.
record Natural {o h e o′ h′ e′} {C : Category o h e} {D : Category o′ h′ e′}
               (F G : Functor C D) : Set (lsuc (o ⊔ h ⊔ e ⊔ o′ ⊔ h′ ⊔ e′)) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module G = Functor G
  field
    η : ∀ X → D.Hom (F.F₀ X) (G.F₀ X)
    square : ∀ {X Y} (f : C.Hom X Y) → G.F₁ f D.∘ η X D.≈ η Y D.∘ F.F₁ f

-- The polymorphism law of §1.6 is precisely a naturality square in Fun.
reversal : Natural Lists Lists
reversal = record { η = λ _ → reverse; square = reverse-natural }

module Vertical {o h e o′ h′ e′} {C : Category o h e} {D : Category o′ h′ e′}
                {F G H : Functor C D} (α : Natural F G) (β : Natural G H) where
  private module C = Category C
  open Category D hiding (identity)
  private module F = Functor F
  private module G = Functor G
  private module H = Functor H
  private module α = Natural α
  private module β = Natural β

  -- Chain equalities of arrows in D, not equalities of Agda terms.
  infixr 2 _≈⟨_⟩_
  _≈⟨_⟩_ : ∀ {X Y} (f : Hom X Y) {g k} → f ≈ g → g ≈ k → f ≈ k
  _ ≈⟨ p ⟩ q = transitive p q

  composite : Natural F H
  Natural.η composite X = β.η X ∘ α.η X
  Natural.square composite {X} {Y} f =
    H.F₁ f ∘ (β.η X ∘ α.η X)  ≈⟨ symmetric (assoc _ _ _) ⟩
    (H.F₁ f ∘ β.η X) ∘ α.η X  ≈⟨ compose-cong (β.square f) reflexive ⟩
    (β.η Y ∘ G.F₁ f) ∘ α.η X  ≈⟨ assoc _ _ _ ⟩
    β.η Y ∘ (G.F₁ f ∘ α.η X)  ≈⟨ compose-cong reflexive (α.square f) ⟩
    β.η Y ∘ (α.η Y ∘ F.F₁ f)  ≈⟨ symmetric (assoc _ _ _) ⟩
    reflexive
