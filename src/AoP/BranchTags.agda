{-# OPTIONS --safe --without-K #-}
module AoP.BranchTags where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Conditions using (choose)
open import Agda.Builtin.Bool
private variable A B C : Set

-- §3.4. A condition routes its input down one of two branches. The
-- branch tag alone recovers the truth value; the payload preserves the
-- original input for the chosen function. This gives the left inverse
-- of exercise 3.25 and the naturality square of 3.26 in Fun.
route : A × Bool → A ⊎ A
route (x , true) = inl x
route (x , false) = inr x

predicate : (A → Bool) → A → A ⊎ A
predicate p x = route (x , p x)

truth : A ⊎ A → Bool
truth (inl _) = true
truth (inr _) = false

recover : (p : A → Bool) → ∀ x → truth (predicate p x) ≡ p x
recover p x with p x
... | true = refl
... | false = refl

injective : (p q : A → Bool) → (∀ x → predicate p x ≡ predicate q x) → ∀ x → p x ≡ q x
injective p q law x with p x | q x | law x
... | true | true | _ = refl
... | false | false | _ = refl
... | true | false | ()
... | false | true | ()

both : (A → B) → A ⊎ A → B ⊎ B
both f (inl x) = inl (f x)
both f (inr x) = inr (f x)

natural : (f : A → B) (x : A) (v : Bool) → both f (route (x , v)) ≡ route (f x , v)
natural f x true = refl
natural f x false = refl

-- Equations 3.4 and 3.5: precomposition changes both branches and the
-- test; a conditional with identical branches forgets the test.
before : (h : A → B) (p : B → Bool) (f g : B → C) → ∀ x →
         choose p f g (h x) ≡ choose (λ a → p (h a)) (λ a → f (h a)) (λ a → g (h a)) x
before h p f g x with p (h x)
... | true = refl
... | false = refl

same : (p : A → Bool) (f : A → B) → ∀ x → choose p f f x ≡ f x
same p f x with p x
... | true = refl
... | false = refl
