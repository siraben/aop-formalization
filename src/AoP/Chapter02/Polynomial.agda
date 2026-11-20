{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.Polynomial where

open import AoP.Common.Prelude

infixr 4 _⊎_
data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

-- Unary polynomial functors, by their expressions (§2.5).
infixr 5 _⊗_
infixr 4 _⊕_
data Poly : Set₁ where
  I : Poly
  K : Set → Poly
  _⊗_ _⊕_ : Poly → Poly → Poly

⟦_⟧ : Poly → Set → Set
⟦ I ⟧ X = X
⟦ K A ⟧ X = A
⟦ F ⊗ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
⟦ F ⊕ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X

map : ∀ F {A B} → (A → B) → ⟦ F ⟧ A → ⟦ F ⟧ B
map I f x = f x
map (K _) f x = x
map (F ⊗ G) f (x , y) = map F f x , map G f y
map (F ⊕ G) f (inl x) = inl (map F f x)
map (F ⊕ G) f (inr y) = inr (map G f y)

identity : ∀ F {A} (x : ⟦ F ⟧ A) → map F (λ a → a) x ≡ x
identity I x = refl
identity (K _) x = refl
identity (F ⊗ G) (x , y) rewrite identity F x | identity G y = refl
identity (F ⊕ G) (inl x) = cong inl (identity F x)
identity (F ⊕ G) (inr y) = cong inr (identity G y)

composition : ∀ F {A B C} (g : B → C) (f : A → B) (x : ⟦ F ⟧ A) →
              map F (λ a → g (f a)) x ≡ map F g (map F f x)
composition I g f x = refl
composition (K _) g f x = refl
composition (F ⊗ G) g f (x , y) rewrite composition F g f x | composition G g f y = refl
composition (F ⊕ G) g f (inl x) = cong inl (composition F g f x)
composition (F ⊕ G) g f (inr y) = cong inr (composition G g f y)

-- Lists solve X ≅ 1 + A × X without a positivity override.
ListF : Set → Poly
ListF A = K ⊤ ⊕ (K A ⊗ I)

roll : ∀ {A} → ⟦ ListF A ⟧ (List A) → List A
roll (inl tt) = []
roll (inr (a , xs)) = a ∷ xs

unroll : ∀ {A} → List A → ⟦ ListF A ⟧ (List A)
unroll [] = inl tt
unroll (a ∷ xs) = inr (a , xs)

roll-unroll : ∀ {A} (xs : List A) → roll (unroll xs) ≡ xs
roll-unroll [] = refl
roll-unroll (_ ∷ _) = refl

unroll-roll : ∀ {A} (p : ⟦ ListF A ⟧ (List A)) → unroll (roll p) ≡ p
unroll-roll (inl tt) = refl
unroll-roll (inr _) = refl
