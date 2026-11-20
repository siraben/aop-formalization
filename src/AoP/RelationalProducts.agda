{-# OPTIONS --safe --without-K #-}
module AoP.RelationalProducts where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
private variable A B C D E F : Set

-- §§5.1–5.2. Relate pairs componentwise: the choices in the left and
-- right coordinates are independent. The arrow notation is target-first.
infixr 8 _⊗_
_⊗_ : (B ← A) → (D ← C) → (B × D ← A × C)
(R ⊗ S) (b , d) (a , c) = R b a × S d c

mono : (R R′ : B ← A) (S S′ : D ← C) → R ⊆ R′ → S ⊆ S′ → R ⊗ S ⊆ R′ ⊗ S′
mono R R′ S S′ l r {b , d} {a , c} (x , y) = l x , r y

id-intro : Id {A × B} ⊆ Id ⊗ Id
id-intro {b = b , d} refl = refl , refl

id-elim : Id ⊗ Id ⊆ Id {A × B}
id-elim {b = b , d} {a , c} (refl , refl) = refl

module Composition (R : B ← A) (S : D ← C) (T : E ← B) (U : F ← D) where
  -- Interchange: two successive pair steps iff each component can take
  -- its two steps. The intermediate pair consists of the two witnesses.
  split : (T ⊗ U) ∘ (R ⊗ S) ⊆ (T ∘ R) ⊗ (U ∘ S)
  split {e , f} {a , c} ((b , d) , (t , u) , (r , s)) = (b , t , r) , (d , u , s)

  combine : (T ∘ R) ⊗ (U ∘ S) ⊆ (T ⊗ U) ∘ (R ⊗ S)
  combine {e , f} {a , c} ((b , t , r) , (d , u , s)) = (b , d) , (t , u) , (r , s)

-- Converse commutes with the product without changing witnesses.
converse : (R : B ← A) (S : D ← C) → (R ⊗ S) ˘ ⊆ R ˘ ⊗ S ˘
converse R S {a , c} {b , d} p = p

unconverse : (R : B ← A) (S : D ← C) → R ˘ ⊗ S ˘ ⊆ (R ⊗ S) ˘
unconverse R S {b , d} {a , c} p = p
