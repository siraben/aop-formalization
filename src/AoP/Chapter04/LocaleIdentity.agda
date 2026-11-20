{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.LocaleIdentity where

open import AoP.Common.Prelude
open import AoP.Chapter04.LocaleRelations using (Frame; module Rel)

-- Exercise 4.18. Define the diagonal grade by joining top over the
-- equality witnesses. This works even on objects without decidable
-- equality. Distributing meet over this join reduces both unit laws
-- to the single path with equal intermediate and endpoint values.
module Law (F : Frame) where
  open Frame F
  open Rel F
  top : V
  top = join (λ (v : V) → v)
  above : ∀ v → v ≤ top
  above v = inject (λ x → x) v
  diag : ∀ {A} → Rel A A
  diag x y = join {x ≡ y} (λ _ → top)
  left-in : ∀ {A B} (R : Rel B A) → R ⊆ (diag ∘ R)
  left-in R b a = chain (pair (chain (above _) (inject _ refl)) (rid _)) (inject (λ i → meet (diag b i) (R i a)) b)
  left-out : ∀ {A B} (R : Rel B A) → (diag ∘ R) ⊆ R
  left-out R b a = least _ λ i → chain (distribute {b ≡ i} (λ _ → top) (R i a)) (least _ (point i))
    where point : ∀ i (e : b ≡ i) → meet top (R i a) ≤ R b a
          point .b refl = right top (R b a)
  right-in : ∀ {A B} (R : Rel B A) → R ⊆ (R ∘ diag)
  right-in R b a = chain (pair (rid _) (chain (above _) (inject _ refl))) (inject (λ i → meet (R b i) (diag i a)) a)
  right-out : ∀ {A B} (R : Rel B A) → (R ∘ diag) ⊆ R
  right-out R b a = least _ λ i → chain (pair (right (R b i) (diag i a)) (left (R b i) (diag i a)))
    (chain (distribute {i ≡ a} (λ _ → top) (R b i)) (least _ (point i)))
    where point : ∀ i (e : i ≡ a) → meet top (R b i) ≤ R b a
          point .a refl = right top (R b a)
