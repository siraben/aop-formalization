{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ListTypeFunctorFusion where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆; unique; fusion)
open import AoP.Chapter02.ListAlgebra using (relabel)
open import AoP.Chapter03.Horner using (map)

-- §2.7, equation (2.13) for lists. The fold defining relabel rebuilds
-- each cons with a changed head. The usual recursive map has those
-- same constructor equations, so uniqueness identifies the programs.
map-is-fold : ∀ {A B : Set} (f : A → B) xs → map f xs ≡ relabel f xs
map-is-fold f = unique (map f) [] (λ a ys → f a ∷ ys) refl (λ a xs → refl)

-- Slide a consumer through relabel: keep its empty case and compose
-- its cons case with f at the head. This instantiates fold fusion;
-- the local square computes because the rebuilt list has a cons there.
consume : ∀ {A B C : Set} (z : C) (k : B → C → C) (f : A → B) xs →
  ⦅ z ∣ k ⦆ (relabel f xs) ≡ ⦅ z ∣ (λ a r → k (f a) r) ⦆ xs
consume z k f = fusion ⦅ z ∣ k ⦆ [] (λ a ys → f a ∷ ys) (λ a r → k (f a) r) (λ _ _ → refl)

-- Specialize the consumer to rebuilding cons cells with g. The fused
-- fold does both relabellings while rebuilding each cell just once.
composition : ∀ {A B C : Set} (g : B → C) (f : A → B) xs →
  relabel g (relabel f xs) ≡ relabel (λ a → g (f a)) xs
composition g f = consume [] (λ b ys → g b ∷ ys) f

open import Agda.Builtin.Nat using (Nat; _+_; suc)

-- (2.14) with addition as consumer: contribute f a at each cell. The
-- right side computes the sum directly without building the mapped list.
sum-after-map : ∀ {A : Set} (f : A → Nat) xs →
  ⦅ 0 ∣ _+_ ⦆ (map f xs) ≡ ⦅ 0 ∣ (λ a r → f a + r) ⦆ xs
sum-after-map f xs = cong ⦅ 0 ∣ _+_ ⦆ (map-is-fold f xs) ∙ consume 0 _+_ f xs

example : ⦅ 0 ∣ _+_ ⦆ (map suc (1 ∷ 3 ∷ 2 ∷ [])) ≡ 9
example = begin
  ⦅ 0 ∣ _+_ ⦆ (map suc (1 ∷ 3 ∷ 2 ∷ []))
    ≡⟨ sum-after-map suc (1 ∷ 3 ∷ 2 ∷ []) ⟩
  ⦅ 0 ∣ (λ a r → suc a + r) ⦆ (1 ∷ 3 ∷ 2 ∷ [])
    ≡⟨⟩
  2 + (4 + (3 + 0)) ≡⟨⟩
  9 ∎
