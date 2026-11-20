{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelationalSums where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Shunting using (Id)
private variable A B C D E F : Set

-- §5.3. A sum step keeps its tag: mixed left/right cases are impossible
-- by construction, even when both component relations are total.
infixr 8 _⊕_
data _⊕_ {A B C D : Set} (R : B ← A) (S : D ← C) : B ⊎ D ← A ⊎ C where
  left  : ∀ {a b} → R b a → (R ⊕ S) (inl b) (inl a)
  right : ∀ {c d} → S d c → (R ⊕ S) (inr d) (inr c)

mono : (R R′ : B ← A) (S S′ : D ← C) → R ⊆ R′ → S ⊆ S′ → R ⊕ S ⊆ R′ ⊕ S′
mono R R′ S S′ p q (left r) = left (p r)
mono R R′ S S′ p q (right s) = right (q s)

id-intro : Id {A ⊎ B} ⊆ Id ⊕ Id
id-intro {b = inl a} refl = left refl
id-intro {b = inr b} refl = right refl

id-elim : Id ⊕ Id ⊆ Id {A ⊎ B}
id-elim (left refl) = refl
id-elim (right refl) = refl

module Composition (R : B ← A) (S : D ← C) (T : E ← B) (U : F ← D) where
  -- The first step fixes the tag of the intermediate witness; the second
  -- cannot switch it. Thus only two of the four apparent branches survive.
  distribute : (T ⊕ U) ∘ (R ⊕ S) ⊆ (T ∘ R) ⊕ (U ∘ S)
  distribute (_ , left t , left r) = left (_ , t , r)
  distribute (_ , right u , right s) = right (_ , u , s)

  collect : (T ∘ R) ⊕ (U ∘ S) ⊆ (T ⊕ U) ∘ (R ⊕ S)
  collect (left (b , t , r)) = inl b , left t , left r
  collect (right (d , u , s)) = inr d , right u , right s

module Converse (R : B ← A) (S : D ← C) where
  distribute : (R ⊕ S) ˘ ⊆ R ˘ ⊕ S ˘
  distribute (left r) = left r
  distribute (right s) = right s

  collect : R ˘ ⊕ S ˘ ⊆ (R ⊕ S) ˘
  collect (left r) = left r
  collect (right s) = right s
