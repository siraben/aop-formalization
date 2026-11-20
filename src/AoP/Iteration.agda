{-# OPTIONS --safe --without-K #-}
module AoP.Iteration where

open import AoP.Prelude
open import AoP.Naturals using (foldn; foldn-unique)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
private variable A B : Set

-- Exercises 3.42–43. Starting with g b, run h exactly n times.
-- Fixing the parameter b turns the two iterator equations into the
-- ordinary natural-number fold equations, so uniqueness follows too.
iter : (B → A) → (A → A) → Nat × B → A
iter g h (n , b) = foldn (g b) h n

unique : (g : B → A) (h : A → A) (k : Nat × B → A) →
         (∀ b → k (0 , b) ≡ g b) → (∀ n b → k (suc n , b) ≡ h (k (n , b))) →
         ∀ p → k p ≡ iter g h p
unique g h k base step (n , b) = foldn-unique (λ i → k (i , b)) (g b) h (base b) (λ i → step i b) n

addition : ∀ m n → m + n ≡ iter (λ x → x) suc (m , n)
addition m n = unique (λ x → x) suc (λ p → fst p + snd p) (λ _ → refl) (λ _ _ → refl) (m , n)

-- Concatenating two runs adds their iteration counts, including when
-- either count is zero. The starting state is arbitrary.
compose : (h : A → A) (m n : Nat) (a : A) →
          iter (λ x → x) h (m + n , a) ≡ iter (λ x → x) h (m , iter (λ x → x) h (n , a))
compose h zero n a = refl
compose h (suc m) n a = cong h (compose h m n a)
