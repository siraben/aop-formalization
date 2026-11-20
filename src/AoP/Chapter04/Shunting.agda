{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.Shunting where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
private variable A B C D : Set

Id : A ← A
Id = _≡_

-- §§4.1–4.2. The graph of a function is entire and simple. Keeping
-- these properties as hypotheses makes shunting work for any such arrow.
record Map (F : B ← A) : Set where
  field
    entire : Id ⊆ F ˘ ∘ F
    simple : F ∘ F ˘ ⊆ Id

module _ (f : A → B) where
  graph : B ← A
  graph b a = f a ≡ b

  is-map : Map graph
  Map.entire is-map refl = _ , refl , refl
  Map.simple is-map (_ , refl , refl) = refl

-- Inclusion calculations need only reassociation, units and monotonicity.
infixr 2 _⊆⟨_⟩_
_⊆⟨_⟩_ : (R : B ← A) {S T : B ← A} → R ⊆ S → S ⊆ T → R ⊆ T
(_ ⊆⟨ p ⟩ q) r = q (p r)

infix 3 _∎⊆
_∎⊆ : (R : B ← A) → R ⊆ R
(R ∎⊆) r = r

post : (S : C ← B) {R T : B ← A} → R ⊆ T → S ∘ R ⊆ S ∘ T
post S p (b , s , r) = b , s , p r

pre : {R T : C ← B} → R ⊆ T → (S : B ← A) → R ∘ S ⊆ T ∘ S
pre p S (b , r , s) = b , p r , s

assoc→ : (T : D ← C) (S : C ← B) (R : B ← A) → (T ∘ S) ∘ R ⊆ T ∘ (S ∘ R)
assoc→ T S R (b , (c , t , s) , r) = c , t , b , s , r

assoc← : (T : D ← C) (S : C ← B) (R : B ← A) → T ∘ (S ∘ R) ⊆ (T ∘ S) ∘ R
assoc← T S R (c , t , b , s , r) = b , (c , t , s) , r

module _ (F : B ← A) (m : Map F) (R : A ← C) (S : B ← C) where
  shunt : F ∘ R ⊆ S → R ⊆ F ˘ ∘ S
  shunt p =
    R                 ⊆⟨ (λ r → _ , refl , r) ⟩
    Id ∘ R            ⊆⟨ pre {R = Id} {T = F ˘ ∘ F} (Map.entire m) R ⟩
    (F ˘ ∘ F) ∘ R     ⊆⟨ assoc→ (F ˘) F R ⟩
    F ˘ ∘ (F ∘ R)     ⊆⟨ post (F ˘) {R = F ∘ R} {T = S} p ⟩
    F ˘ ∘ S ∎⊆

  unshunt : R ⊆ F ˘ ∘ S → F ∘ R ⊆ S
  unshunt p =
    F ∘ R             ⊆⟨ post F {R = R} {T = F ˘ ∘ S} p ⟩
    F ∘ (F ˘ ∘ S)     ⊆⟨ assoc← F (F ˘) S ⟩
    (F ∘ F ˘) ∘ S     ⊆⟨ pre {R = F ∘ F ˘} {T = Id} (Map.simple m) S ⟩
    Id ∘ S            ⊆⟨ (λ { (_ , refl , s) → s }) ⟩
    S ∎⊆
