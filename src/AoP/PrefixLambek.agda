{-# OPTIONS --safe --without-K #-}
module AoP.PrefixLambek where

open import AoP.Prelude
open import AoP.Categories using (Category)
open import AoP.Functors using (Functor)
open import Agda.Primitive using (Level; lzero)

-- Exercise 6.5. Objects can themselves be arrows of an allegory,
-- ordered by inclusion. Parallel arrows in this new category are
-- indistinguishable, irrespective of their inclusion witnesses.
module Law {c r : Level} {L : Set c} (_≤_ : L → L → Set r)
           (id≤ : ∀ x → x ≤ x) (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
           (Φ : L → L) (mono : ∀ {x y} → x ≤ y → Φ x ≤ Φ y) where
  C : Category c r lzero
  C = record { Obj = L; Hom = _≤_; _≈_ = λ _ _ → ⊤; identity = id≤ _
             ; _∘_ = λ g f → trans f g; reflexive = tt; symmetric = λ _ → tt
             ; transitive = λ _ _ → tt; compose-cong = λ _ _ → tt
             ; unitˡ = λ _ → tt; unitʳ = λ _ → tt; assoc = λ _ _ _ → tt }
  F : Functor C C
  F = record { F₀ = Φ; F₁ = mono; resp = λ _ → tt; identity = tt; composition = λ _ _ → tt }
  module C = Category C
  module F = Functor F
  Alg : L → Set r
  Alg x = C.Hom (F.F₀ x) x
  module Least {μ} (inn : Alg μ) (fold : ∀ {x} → Alg x → μ ≤ x) where
    square : ∀ {x} (a : Alg x) → (fold a C.∘ inn) C.≈ (a C.∘ F.F₁ (fold a))
    square a = tt
    unique : ∀ {x} (a : Alg x) (h : μ ≤ x) → h C.≈ fold a
    unique a h = tt
    -- Fold into the lifted constructor, exactly as in Lambek's lemma.
    out : μ ≤ Φ μ
    out = fold (F.F₁ inn)
    section : (inn C.∘ out) C.≈ C.identity
    section = tt
    retraction : (out C.∘ inn) C.≈ C.identity
    retraction = tt
    fixed : (∀ {x y} → x ≤ y → y ≤ x → x ≡ y) → Φ μ ≡ μ
    fixed anti = anti inn out
