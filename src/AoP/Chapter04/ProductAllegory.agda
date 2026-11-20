{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ProductAllegory where

open import AoP.Chapter02.Categories using (Category)
open import AoP.Chapter02.ProductCategory using (module Product)
open import AoP.Chapter02.ArrowCategory using (_×_)
open import Agda.Builtin.Sigma using (fst; snd; _,_)
open import Agda.Primitive using (Level; _⊔_; lsuc)

-- Exercise 4.7. Equip a category with ordered homs, binary meets,
-- converse and the modular law. Equality on arrows is the category's
-- own equivalence; no propositional equality of relations is needed.
record Laws {o h e} (C : Category o h e) (p : Level) : Set (o ⊔ h ⊔ e ⊔ lsuc p) where
  open Category C
  field
    _⊑_ : ∀ {a b} → Hom a b → Hom a b → Set p
    respect : ∀ {a b} {f g : Hom a b} → f ≈ g → f ⊑ g
    trans : ∀ {a b} {f g k : Hom a b} → f ⊑ g → g ⊑ k → f ⊑ k
    antisym : ∀ {a b} {f g : Hom a b} → f ⊑ g → g ⊑ f → f ≈ g
    meet : ∀ {a b} → Hom a b → Hom a b → Hom a b
    lower₁ : ∀ {a b} (f g : Hom a b) → meet f g ⊑ f
    lower₂ : ∀ {a b} (f g : Hom a b) → meet f g ⊑ g
    glb : ∀ {a b} {f g k : Hom a b} → k ⊑ f → k ⊑ g → k ⊑ meet f g
    rev : ∀ {a b} → Hom a b → Hom b a
    invol : ∀ {a b} (f : Hom a b) → rev (rev f) ≈ f
    flip : ∀ {a b c} (g : Hom b c) (f : Hom a b) → rev (g ∘ f) ≈ (rev f ∘ rev g)
    rev-mono : ∀ {a b} {f g : Hom a b} → f ⊑ g → rev f ⊑ rev g
    mono : ∀ {a b c} {f f′ : Hom a b} {g g′ : Hom b c} → g ⊑ g′ → f ⊑ f′ → (g ∘ f) ⊑ (g′ ∘ f′)
    modular : ∀ {a b c} (g : Hom b c) (f : Hom a b) (k : Hom a c) → meet (g ∘ f) k ⊑ (g ∘ meet f (rev g ∘ k))

module Pair {o h e p o′ h′ e′ p′} {C : Category o h e} {D : Category o′ h′ e′}
            (left : Laws C p) (right : Laws D p′) where
  private module L = Laws left
  private module R = Laws right
  product : Laws (Product.prod C D) (p ⊔ p′)
  Laws._⊑_ product f g = (fst f L.⊑ fst g) × (snd f R.⊑ snd g)
  Laws.respect product (x , y) = L.respect x , R.respect y
  Laws.trans product (x , y) (u , v) = L.trans x u , R.trans y v
  Laws.antisym product (x , y) (u , v) = L.antisym x u , R.antisym y v
  Laws.meet product f g = L.meet (fst f) (fst g) , R.meet (snd f) (snd g)
  Laws.lower₁ product f g = L.lower₁ _ _ , R.lower₁ _ _
  Laws.lower₂ product f g = L.lower₂ _ _ , R.lower₂ _ _
  Laws.glb product (x , y) (u , v) = L.glb x u , R.glb y v
  Laws.rev product f = L.rev (fst f) , R.rev (snd f)
  Laws.invol product f = L.invol _ , R.invol _
  Laws.flip product g f = L.flip _ _ , R.flip _ _
  Laws.rev-mono product (x , y) = L.rev-mono x , R.rev-mono y
  Laws.mono product (x , y) (u , v) = L.mono x u , R.mono y v
  Laws.modular product g f k = L.modular (fst g) (fst f) (fst k) , R.modular (snd g) (snd f) (snd k)
