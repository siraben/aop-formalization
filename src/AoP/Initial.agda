{-# OPTIONS --safe --without-K #-}
module AoP.Initial where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)

-- §2.6, in the category of sets and total functions. An F-algebra on A
-- consumes one layer F A. A homomorphism can be pushed through that layer.
module Theory (F : Functor Fun Fun) where
  open Functor F renaming (F₀ to Layer; F₁ to map)

  Algebra : Set → Set
  Algebra A = Layer A → A

  Hom : ∀ {A B} → Algebra A → Algebra B → (A → B) → Set
  Hom a b h = ∀ t → h (a t) ≡ b (map h t)

  record Initial : Set₁ where
    field
      μ : Set
      inn : Algebra μ
      ⦅_⦆ : ∀ {A} → Algebra A → μ → A
      computation : ∀ {A} (a : Algebra A) → Hom inn a ⦅ a ⦆
      unique : ∀ {A} (a : Algebra A) (h : μ → A) → Hom inn a h →
               ∀ x → h x ≡ ⦅ a ⦆ x

  module Laws (I : Initial) where
    open Initial I

    -- Reflection: identity already solves the defining fold equation.
    reflection : ∀ x → x ≡ ⦅ inn ⦆ x
    reflection = unique inn (λ x → x) λ t → cong inn (sym (identity t))
      where
      sym : ∀ {A : Set} {u v : A} → u ≡ v → v ≡ u
      sym refl = refl

    fusion : ∀ {A B} (a : Algebra A) (b : Algebra B) (h : A → B) →
             Hom a b h → ∀ x → h (⦅ a ⦆ x) ≡ ⦅ b ⦆ x
    fusion a b h square = unique b (λ x → h (⦅ a ⦆ x)) λ t → begin
      h (⦅ a ⦆ (inn t))
        ≡⟨ cong h (computation a t) ⟩
      h (a (map ⦅ a ⦆ t))
        ≡⟨ square (map ⦅ a ⦆ t) ⟩
      b (map h (map ⦅ a ⦆ t))
        ≡⟨ cong b (back (composition h ⦅ a ⦆ t)) ⟩
      b (map (λ x → h (⦅ a ⦆ x)) t) ∎
      where
      back : ∀ {A : Set} {u v : A} → u ≡ v → v ≡ u
      back refl = refl
