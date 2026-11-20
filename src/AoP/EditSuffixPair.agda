{-# OPTIONS --safe --without-K #-}
module AoP.EditSuffixPair where

open import AoP.Prelude
open import AoP.EditScript
open import AoP.EditTail using (module Law)
open import AoP.EditSourceTail using (module Source)
open import AoP.EditSuffix using (module Target; module Lift)
open import AoP.Closure using (module Paths)
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.NatOrder using (rid; chain)

-- §9.2: independently discard prefixes of the source and target.
-- We embed each one-string path into an endpoint-pair path and
-- concatenate them, so either prefix may be empty or the whole string.
module Both {A : Set} where
  open Scripts {A} using (Strings)
  open Target {A} using (E; R)
  data Tail : List A ← List A where
    pop : ∀ {x xs} → Tail xs (x ∷ xs)
  data Move : Strings ← Strings where
    left : ∀ {x z y} → Tail z x → Move (z , y) (x , y)
    right : ∀ {y z x} → Tail z y → Move (x , z) (x , y)
  step : Move ∘ E ⊆ E ∘ R
  step {a = es} (_ , left (pop {a}) , eq) = Source.shorten es a _ _ eq
  step {a = es} (_ , right (pop {b}) , eq) = Law.tail-script es _ b _ eq
  left-path : ∀ {x z} y → Paths.Star Tail z x → Paths.Star Move (z , y) (x , y)
  left-path y Paths.stop = Paths.stop
  left-path y (Paths.extend e p) = Paths.extend (left e) (left-path y p)
  right-path : ∀ {y z} x → Paths.Star Tail z y → Paths.Star Move (x , z) (x , y)
  right-path x Paths.stop = Paths.stop
  right-path x (Paths.extend e p) = Paths.extend (right e) (right-path x p)
  suffix-pair : ∀ {x y u v es} → Paths.Star Tail u x → Paths.Star Tail v y → E (x , y) es → (E ∘ R) (u , v) es
  suffix-pair {y = y} {u} sx sy eq = Lift.follow Move E R (λ _ → rid _) chain step
    (Paths.append Move (_ , right-path u sy , left-path y sx)) eq
