{-# OPTIONS --safe --without-K #-}
module AoP.ResidualConnections where

open import AoP.Prelude
open import AoP.Relations
open import AoP.LeftDivision using (_＼_; residual; cancel-left)
open import AoP.RelDifference using (_−_; Decides; remove; cover)
open import AoP.Complement using (_⊔_)
private variable A B C : Set

-- Exercise 4.36. The variable relation determines which map is the
-- lower adjoint. Fix a factor R: composition by R goes on the left
-- of inclusion and division by R goes on the right. Fix a set of
-- edges S: removing S on the left corresponds to adjoining S on the
-- right. For subtraction the constructive cover law needs decidable S.
module Connections {U V W Z : Set} (L : (U ← V) → W ← Z) (G : (W ← Z) → U ← V) where
  record Connection : Set₁ where
    field
      up : ∀ X Y → L X ⊆ Y → X ⊆ G Y
      down : ∀ X Y → X ⊆ G Y → L X ⊆ Y

    lower-mono : ∀ X X′ → X ⊆ X′ → L X ⊆ L X′
    lower-mono X X′ inc = down X (L X′) (λ x → up X′ (L X′) (λ y → y) (inc x))
    upper-mono : ∀ Y Y′ → Y ⊆ Y′ → G Y ⊆ G Y′
    upper-mono Y Y′ inc = up (G Y) Y′ (λ y → inc (down (G Y) Y (λ x → x) y))

open Connections using (Connection)

left-division : (R : C ← B) → Connection {U = B} {V = A} (R ∘_) (R ＼_)
Connections.Connection.up (left-division R) X Y = residual R Y X
Connections.Connection.down (left-division R) X Y = cancel-left R Y X

right-division : (R : B ← A) → Connection {U = C} (_∘ R) (_／ R)
Connections.Connection.up (right-division R) X Y = residuate X R Y
Connections.Connection.down (right-division R) X Y = cancel X R Y

subtraction : (S : B ← A) → Decides S → Connection (_− S) (S ⊔_)
Connections.Connection.up (subtraction S dec) X Y = cover X S Y dec
Connections.Connection.down (subtraction S dec) X Y = remove X S Y
