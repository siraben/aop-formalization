{-# OPTIONS --safe --without-K #-}
module AoP.PostWhiskering where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.Whiskering using (module Through)

-- §2.3. Apply H to every edge of a naturality square. The two paths
-- around the new square are composites in C. Bring the first path
-- inside H, use the original square, then take the second path out.
module Apply {o h e o′ h′ e′ o″ h″ e″} {A : Category o h e}
             {B : Category o′ h′ e′} {C : Category o″ h″ e″}
             (H : Functor B C) {F G : Functor A B} (α : Natural F G) where
  private module H = Functor H
  private module F = Functor F
  private module G = Functor G
  private module α = Natural α
  private module B = Category B
  open Category C
  private
    infixr 2 _≈⟨_⟩_
    _≈⟨_⟩_ : ∀ {X Y} (f : Hom X Y) {g k} → f ≈ g → g ≈ k → f ≈ k
    _ ≈⟨ p ⟩ q = transitive p q
  lift : Natural (Through.compose F H) (Through.compose G H)
  Natural.η lift X = H.F₁ (α.η X)
  Natural.square lift {X} {Y} f =
    H.F₁ (G.F₁ f) ∘ H.F₁ (α.η X) ≈⟨ symmetric (H.composition _ _) ⟩
    H.F₁ (G.F₁ f B.∘ α.η X) ≈⟨ H.resp (α.square f) ⟩
    H.F₁ (α.η Y B.∘ F.F₁ f) ≈⟨ H.composition _ _ ⟩
    reflexive
