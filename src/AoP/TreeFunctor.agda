{-# OPTIONS --safe --without-K #-}
module AoP.TreeFunctor where

open import AoP.Prelude
open import AoP.Trees using (Tree; bin; tip; map)
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
private variable A B C : Set

-- Exercise 2.12. Apply a function at each tip, leaving forks in place.
-- Each functor law therefore reduces at a fork to the laws on its two
-- subtrees. The congruence argument spells out both replacements.
fork-cong : ∀ {l l′ r r′ : Tree A} → l ≡ l′ → r ≡ r′ → bin l r ≡ bin l′ r′
fork-cong {l = l} {l′} {r} {r′} p q = begin
  bin l r   ≡⟨ cong (λ t → bin t r) p ⟩
  bin l′ r  ≡⟨ cong (bin l′) q ⟩
  bin l′ r′ ∎

respect : ∀ {f g : A → B} → (∀ a → f a ≡ g a) → ∀ t → map f t ≡ map g t
respect eq (tip a) = cong tip (eq a)
respect eq (bin l r) = fork-cong (respect eq l) (respect eq r)

unit : (t : Tree A) → map (λ a → a) t ≡ t
unit (tip a) = refl
unit (bin l r) = fork-cong (unit l) (unit r)

fusion : (g : B → C) (f : A → B) (t : Tree A) → map (λ a → g (f a)) t ≡ map g (map f t)
fusion g f (tip a) = refl
fusion g f (bin l r) = fork-cong (fusion g f l) (fusion g f r)

Trees : Functor Fun Fun
Trees = record { F₀ = Tree; F₁ = map; resp = respect; identity = unit; composition = fusion }
