{-# OPTIONS --safe --without-K #-}
module AoP.ConversionCost where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.ConversionFold using (convert)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
private variable A : Set

-- §1.3. Count cons cells allocated while converting a snoc-list.
-- Appending a singleton copies the whole converted prefix and allocates
-- one cell for the new element. The accumulator allocates just that one.
len : List A → Nat
len [] = zero
len (_ ∷ xs) = suc (len xs)

size : Snoc A → Nat
size ε = zero
size (xs ▻ _) = suc (size xs)

singleton-length : (xs : List A) (a : A) → len (xs ++ (a ∷ [])) ≡ suc (len xs)
singleton-length [] a = refl
singleton-length (x ∷ xs) a = cong suc (singleton-length xs a)

preserves-length : (xs : Snoc A) → len (convert xs) ≡ size xs
preserves-length ε = refl
preserves-length (xs ▻ a) = singleton-length (convert xs) a ∙ cong suc (preserves-length xs)

slow fast : Snoc A → Nat
slow ε = 0
slow (xs ▻ _) = suc (len (convert xs)) + slow xs
fast ε = 0
fast (xs ▻ _) = suc (fast xs)

triangle : Nat → Nat
triangle zero = 0
triangle (suc n) = suc n + triangle n

slow-cost : (xs : Snoc A) → slow xs ≡ triangle (size xs)
slow-cost ε = refl
slow-cost (xs ▻ a) rewrite preserves-length xs | slow-cost xs = refl

fast-cost : (xs : Snoc A) → fast xs ≡ size xs
fast-cost ε = refl
fast-cost (xs ▻ a) = cong suc (fast-cost xs)

-- Converting four elements allocates ten cells with repeated append.
four : triangle 4 ≡ 10
four = refl
