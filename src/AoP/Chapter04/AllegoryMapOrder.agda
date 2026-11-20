{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.AllegoryMapOrder where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §4.2. An entire arrow f chooses some output at every input. If
-- f lies below a simple arrow g, g cannot have an additional output.
-- The calculation proves this without elements, even for an allegory
-- in which functions are not represented by Agda functions.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  private
    rid : ∀ {A B} {r : Hom A B} → r ⊑ r
    rid = respect reflexive
    infixr 2 _⊑⟨_⟩_
    _⊑⟨_⟩_ : ∀ {A B} (x : Hom A B) {y z} → x ⊑ y → y ⊑ z → x ⊑ z
    _ ⊑⟨ le ⟩ rest = trans le rest
  discrete : ∀ {A B} (f g : Hom A B) → identity ⊑ (rev f ∘ f) → (g ∘ rev g) ⊑ identity → f ⊑ g → f ≈ g
  discrete f g entire simple sub = antisym sub (g
    ⊑⟨ respect (symmetric (unitʳ g)) ⟩
    g ∘ identity ⊑⟨ mono rid entire ⟩
    g ∘ (rev f ∘ f) ⊑⟨ respect (symmetric (assoc g _ f)) ⟩
    (g ∘ rev f) ∘ f ⊑⟨ mono (mono rid (rev-mono sub)) rid ⟩
    (g ∘ rev g) ∘ f ⊑⟨ mono simple rid ⟩
    identity ∘ f ⊑⟨ respect (unitˡ f) ⟩ rid)
