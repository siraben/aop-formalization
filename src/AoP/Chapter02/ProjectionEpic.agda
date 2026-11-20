{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ProjectionEpic where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Cancellation using (module Laws′)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open Laws′ Fun

-- Exercise 2.28. In Fun a coproduct injection remembers the input,
-- so equality after either injection gives equality before it.
left-monic : ∀ {A B : Set} → Monic (inl {A = A} {B = B})
left-monic f g same x with f x | g x | same x
... | a | .a | refl = refl

right-monic : ∀ {A B : Set} → Monic (inr {A = A} {B = B})
right-monic f g same x with f x | g x | same x
... | b | .b | refl = refl

-- A fixed second coordinate makes every first coordinate reachable.
-- Dually in the two coordinates, a fixed first coordinate suffices for
-- the second projection. Empty factors show why the hypotheses matter.
first-epic : ∀ {A B : Set} → B → Epic (fst {A = A} {B = λ _ → B})
first-epic b f g same a = same (a , b)

second-epic : ∀ {A B : Set} → A → Epic (λ (p : A × B) → snd p)
second-epic a f g same b = same (a , b)

first-fails : Epic (λ (p : ⊤ × ⊥) → fst p) → ⊥
first-fails epic with epic (λ _ → true) (λ _ → false) (λ { (_ , ()) }) tt
... | ()

second-fails : Epic (λ (p : ⊥ × ⊤) → snd p) → ⊥
second-fails epic with epic (λ _ → true) (λ _ → false) (λ { (() , _) }) tt
... | ()

-- Categorical duality sends Fun to its opposite. It does not identify
-- every theorem of Fun with its arrow-reversal inside Fun itself.
