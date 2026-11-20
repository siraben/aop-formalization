{-# OPTIONS --safe --without-K #-}
module AoP.InfiniteChoices where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Complement using (⊥)

-- Exercise 8.20, a scope obstruction. For the function-space functor
-- T A = Nat → A, give each position the two-element Boolean menu.
-- Every Boolean stream is a legitimate choice. No finite list can
-- represent all of them, even up to pointwise equality.
Stream = Nat → Bool
flip : Bool → Bool
flip false = true
flip true = false
miss : ∀ b → flip b ≡ b → ⊥
miss false ()
miss true ()

-- The list is structurally smaller before shifting the diagonal.
-- Shift the index instead of mapping tail over all remaining streams.
diag : List Stream → Nat → Stream
diag [] i n = false
diag (f ∷ fs) i zero = flip (f i)
diag (f ∷ fs) i (suc n) = diag fs (suc i) n

advance : Nat → Nat → Nat
advance i zero = i
advance i (suc n) = advance (suc i) n

outside : ∀ fs i {f} → f ∈ fs → (∀ n → diag fs i n ≡ f (advance i n)) → ⊥
outside (f ∷ fs) i here eq = miss (f i) (eq zero)
outside (g ∷ fs) i (there m) eq = outside fs (suc i) m (λ n → eq (suc n))

start : ∀ i n → advance (suc i) n ≡ suc (advance i n)
start i zero = refl
start i (suc n) = start (suc i) n
origin : ∀ n → advance zero n ≡ n
origin zero = refl
origin (suc n) = start zero n ∙ cong suc (origin n)

no-list : ∀ fs → (∀ s → Σ Stream λ f → (f ∈ fs) × (∀ n → s n ≡ f n)) → ⊥
no-list fs all with all (diag fs zero)
... | f , m , eq = outside fs zero m (λ n → eq n ∙ cong f (back (origin n)))
  where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
        back refl = refl
