{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ListAlgebra where

open import AoP.Common.Prelude
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Initial using (module Theory)
open import AoP.Chapter02.Polynomial using (ListF; ⟦_⟧; inl; inr; roll)
open import AoP.Chapter02.Folds using (⦅_∣_⦆; unique)

-- Freeze the element parameter A of the list bifunctor. Only the tail
-- position is recursive, so changing that position leaves the head intact.
module Cons (A : Set) where
  Layer = ⟦ ListF A ⟧
  lift : ∀ {X Y} → (X → Y) → Layer X → Layer Y
  lift f (inl tt) = inl tt
  lift f (inr (a , x)) = inr (a , f x)

  layerF : Functor Fun Fun
  layerF = record
    { F₀ = Layer; F₁ = lift
    ; resp = λ { eq (inl tt) → refl; eq (inr (a , x)) → cong (λ y → inr (a , y)) (eq x) }
    ; identity = λ { (inl tt) → refl; (inr _) → refl }
    ; composition = λ { g f (inl tt) → refl; g f (inr _) → refl } }

  module T = Theory layerF
  initial : T.Initial
  T.Initial.μ initial = List A
  T.Initial.inn initial = roll
  T.Initial.⦅_⦆ initial alg = ⦅ alg (inl tt) ∣ (λ a x → alg (inr (a , x))) ⦆
  T.Initial.computation initial alg (inl tt) = refl
  T.Initial.computation initial alg (inr _) = refl
  T.Initial.unique initial alg h law =
    unique h _ _ (law (inl tt)) (λ a xs → law (inr (a , xs)))

-- §2.7. Let a function on labels pass through a list by folding into the
-- constructor algebra for the new labels. No recursive call is needed here.
relabel : ∀ {A B : Set} → (A → B) → List A → List B
relabel {A} f = Cons.T.Initial.⦅_⦆ (Cons.initial A)
                (λ { (inl tt) → []; (inr (a , xs)) → f a ∷ xs })
