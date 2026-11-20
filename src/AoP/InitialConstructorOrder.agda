{-# OPTIONS --safe --without-K #-}
module AoP.InitialConstructorOrder where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Shunting using (graph)

-- 7.34. Fold into the subtype of self-related points. The first
-- projection forgets the certificate and is an algebra homomorphism;
-- initiality forces the projected fold to be the identity.
module Proof (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Theory F
  open Initial I
  open Functor F using () renaming (F₀ to Layer; F₁ to map)
  module Lift (L : ∀ {A B} → B ← A → Layer B ← Layer A)
    (graphs : ∀ {A B} (f : A → B) → graph (map f) ⊆ L (graph f))
    (back : ∀ {A B} (R : B ← A) → (L R) ˘ ⊆ L (R ˘))
    (join : ∀ {A B C} (P : C ← B) (Q : B ← A) → L P ∘ L Q ⊆ L (P ∘ Q))
    (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → L P ⊆ L Q)
    (R : μ ← μ) (ordered : ∀ {x y} → L R x y → R (inn x) (inn y)) where
    Good = Σ μ λ x → R x x
    val : Good → μ
    val = fst
    diagonal : graph val ∘ graph val ˘ ⊆ R
    diagonal ((x , xx) , refl , refl) = xx
    algebra : Algebra Good
    algebra t = inn (map val t) , ordered (mono (graph val ∘ graph val ˘) R diagonal
      (join (graph val) (graph val ˘) (t , graphs val refl , back (graph val) (graphs val refl))))
    forget : ∀ x → val (⦅ algebra ⦆ x) ≡ x
    forget x = Laws.fusion I algebra inn val (λ _ → refl) x ∙ rev (Laws.reflection I x)
      where rev : ∀ {x y : μ} → x ≡ y → y ≡ x
            rev refl = refl
    reflexive : ∀ x → R x x
    reflexive x = transport (forget x) (snd (⦅ algebra ⦆ x))
      where transport : ∀ {a b} → a ≡ b → R a a → R b b
            transport refl r = r
