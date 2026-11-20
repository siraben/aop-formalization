{-# OPTIONS --safe --without-K #-}
module AoP.BinaryModulus where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; rid)
open import AoP.Polynomial using (inl; inr)
open import AoP.HalvingRun using (low; half; smaller)
open import AoP.HalvingDigits using (shift; reconstruct)
open import AoP.ModulusStep using (module At)

-- §6.4. A certificate for n mod b consists of a remainder below b
-- and a derivation of n by repeatedly adding b to that remainder.
-- When a bit arrives, each previous copy of b becomes two copies.
module Compute (k : Nat) where
  open At k
  data Copies (r : Nat) : Nat → Set where
    same : Copies r r
    add : ∀ {n} → Copies r n → Copies r (b + n)

  private
    slide : ∀ x y → x + suc y ≡ suc (x + y)
    slide zero y = refl
    slide (suc x) y = cong suc (slide x y)
    sym : ∀ {x y : Nat} → x ≡ y → y ≡ x
    sym refl = refl
    subst : (P : Nat → Set) → ∀ {x y} → x ≡ y → P x → P y
    subst P refl p = p
    distribute : ∀ t x n → shift t (x + n) ≡ x + (x + shift t n)
    distribute t zero n = refl
    distribute t (suc x) n = AoP.HalvingDigits.advance t (x + n) ∙
      cong (λ y → suc (suc y)) (distribute t x n) ∙ cong suc (sym (slide x _))

    lift : ∀ t {r n} → Copies r n → ∀ {s} → Copies s (shift t r) → Copies s (shift t n)
    lift t same q = q
    lift t (add {n} p) q rewrite distribute t b n = add (add (lift t p q))

  Answer : Nat → Set
  Answer n = Σ Nat λ r → (r ≤ k) × Copies r n

  digit : ∀ t {n} → Answer n → Answer (shift t n)
  digit t (r , bound , p) with update t r bound
  ... | result s ok (inl refl) = s , ok , lift t p same
  ... | result s ok (inr eq) = s , ok , lift t p (subst (Copies s) eq (add same))

  bounded : ∀ fuel n → n ≤ fuel → Answer n
  bounded fuel zero h = 0 , z≤ , same
  bounded (suc fuel) (suc n) (s≤ h) = subst Answer (reconstruct (suc n))
    (digit (low (suc n)) (bounded fuel _ (chain (smaller n) h)))

  solve : ∀ n → Answer n
  solve n = bounded n n (rid n)

example : fst (Compute.solve 4 53) ≡ 3
example = refl
