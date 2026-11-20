{-# OPTIONS --safe --without-K #-}
module AoP.LongestPrefix where

open import AoP.Prelude
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (inl; inr)
open import AoP.Naturality using (_++_)
open import AoP.Complement using (⊥)
open import AoP.Reserves
open import AoP.SecureBlock
open import AoP.NatOrder using (z≤)
open import Agda.Builtin.Nat using (Nat)

-- §7.5. Walk through the transactions until the next extension fails.
-- Prefix closure explains why that first failure also rules out every
-- longer block. The result records the suffix for the next van visit.
module Prefix {A : Set} where
  data _≼_ : List A → List A → Set where
    nil : ∀ {xs} → [] ≼ xs
    cons : ∀ {a xs ys} → xs ≼ ys → (a ∷ xs) ≼ (a ∷ ys)

  record Longest (P : List A → Set) (xs : List A) : Set where
    constructor result
    field
      block rest : List A
      split : block ++ rest ≡ xs
      fits : P block
      dominates : ∀ {ys} → ys ≼ xs → P ys → ys ≼ block

  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()

  scan : ∀ xs (P : List A → Set) → P [] → (∀ ys → Dec (P ys)) →
         (∀ {ys zs} → ys ≼ zs → P zs → P ys) → Longest P xs
  scan [] P empty test down = result [] [] refl empty (λ { nil _ → nil })
  scan (x ∷ xs) P empty test down with test (x ∷ [])
  ... | inr no = result [] (x ∷ xs) refl empty λ where
    nil _ → nil
    (cons p) ok → absurd (no (down (cons nil) ok))
  ... | inl ok with scan xs (λ ys → P (x ∷ ys)) ok (λ ys → test (x ∷ ys)) (λ p → down (cons p))
  ...   | result b r eq fits longest = result (x ∷ b) r (cong (x ∷_) eq) fits λ where
    nil _ → nil
    (cons p) yes → cons (longest p yes)

module Van (cap : Nat) where
  open Bank cap
  open Prefix {Tx}
  truncate : ∀ {xs ys a b} → xs ≼ ys → Run ys a b → Σ Nat λ c → Run xs a c
  truncate nil (stop fits) = _ , stop fits
  truncate nil (post fits _ _) = _ , stop fits
  truncate (cons p) (post fits change run) with truncate p run
  ... | c , shorter = c , post fits change shorter

  first-block : ∀ xs → Longest Secure xs
  first-block xs = scan xs Secure (0 , 0 , stop z≤) (Check.secure? cap) λ where
    p (a , b , run) → a , truncate p run
