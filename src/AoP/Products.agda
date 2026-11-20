{-# OPTIONS --safe --without-K #-}
module AoP.Products where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
private variable A B C D : Set

-- §2.5 in Fun. Pairing has one input and two observers; a case split
-- dually has two constructors and one output. Arrows are compared pointwise.
⟨_,_⟩ : (C → A) → (C → B) → C → A × B
⟨ f , g ⟩ x = f x , g x

[_,_] : (A → C) → (B → C) → A ⊎ B → C
[ f , g ] (inl a) = f a
[ f , g ] (inr b) = g b

-- Any candidate arrow with the prescribed projections is the pairing.
pair-unique : (h : C → A × B) (f : C → A) (g : C → B) →
              (∀ x → fst (h x) ≡ f x) → (∀ x → snd (h x) ≡ g x) →
              ∀ x → h x ≡ ⟨ f , g ⟩ x
pair-unique h f g l r x = begin
  h x
    ≡⟨⟩  -- product η
  (fst (h x) , snd (h x))
    ≡⟨ cong (_, snd (h x)) (l x) ⟩
  (f x , snd (h x))
    ≡⟨ cong (f x ,_) (r x) ⟩
  ⟨ f , g ⟩ x ∎

case-unique : (h : A ⊎ B → C) (f : A → C) (g : B → C) →
              (∀ x → h (inl x) ≡ f x) → (∀ y → h (inr y) ≡ g y) →
              ∀ z → h z ≡ [ f , g ] z
case-unique h f g l r (inl x) = l x
case-unique h f g l r (inr y) = r y

-- Fusion needs no new induction: the projection/injection equations are
-- all that the two universal properties ask us to verify.
pair-fusion : (f : B → C) (g : B → D) (h : A → B) →
              ∀ x → ⟨ f , g ⟩ (h x) ≡ ⟨ (λ y → f (h y)) , (λ y → g (h y)) ⟩ x
pair-fusion f g h = pair-unique (λ x → ⟨ f , g ⟩ (h x)) _ _ (λ _ → refl) (λ _ → refl)

case-fusion : (h : C → D) (f : A → C) (g : B → C) →
              ∀ z → h ([ f , g ] z) ≡ [ (λ x → h (f x)) , (λ y → h (g y)) ] z
case-fusion h f g = case-unique (λ z → h ([ f , g ] z)) _ _ (λ _ → refl) (λ _ → refl)
