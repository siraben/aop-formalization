{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.LazyPair where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)

-- Exercise 2.31. Model the observable outer constructor of a lazy
-- pair separately from the definedness of its fields. `nothing` at the
-- outer level represents divergence while evaluating to a constructor.
-- Case analysis can see a pair without forcing either of its fields.
LazyPair : Set → Set → Set
LazyPair A B = Maybe (Maybe A × Maybe B)

left : ∀ {A B} → LazyPair A B → Maybe A
left nothing = nothing
left (just p) = fst p
right : ∀ {A B} → LazyPair A B → Maybe B
right nothing = nothing
right (just p) = snd p

-- Two programs on unit: one never produces a pair; the other produces
-- a pair whose fields never return. Both projections agree everywhere.
diverge fields : ⊤ → LazyPair ⊤ ⊤
diverge _ = nothing
fields _ = just (nothing , nothing)

same-left : ∀ x → left (diverge x) ≡ left (fields x)
same-left _ = refl
same-right : ∀ x → right (diverge x) ≡ right (fields x)
same-right _ = refl

-- A context that only demands the constructor separates the programs.
observe : ∀ {A B} → LazyPair A B → Maybe ⊤
observe nothing = nothing
observe (just _) = just tt

different : observe (diverge tt) ≡ observe (fields tt) → ⊥
different ()

-- Pairing cannot have the categorical uniqueness property in this
-- model of a language with observable pair constructors.
no-uniqueness : ((f g : ⊤ → LazyPair ⊤ ⊤) →
  (∀ x → left (f x) ≡ left (g x)) → (∀ x → right (f x) ≡ right (g x)) →
  ∀ x → f x ≡ g x) → ⊥
no-uniqueness unique = different (cong observe (unique diverge fields same-left same-right tt))
