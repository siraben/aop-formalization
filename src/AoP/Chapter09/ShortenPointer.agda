{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ShortenPointer where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter09.Compression using (module Text)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 9.17, the pointer case. A copy reads from the growing
-- buffer, so its source can overlap its destination. Shorten a
-- successful copy by one iteration and identify the omitted letter.
module Law {A : Set} where
  open Text {A}
  shorten : ∀ i k xs {ys} → copy i (suc k) xs ≡ just ys →
            Σ (List A) λ zs → Σ A λ a → (copy i k xs ≡ just zs) × (ys ≡ (zs ++ (a ∷ [])))
  shorten i 0 xs eq with lookup i xs
  ... | nothing with eq
  ...   | ()
  shorten i 0 xs eq | just a with eq
  ... | refl = xs , a , refl , refl
  shorten i (suc k) xs eq with lookup i xs
  ... | nothing with eq
  ...   | ()
  shorten i (suc k) xs eq | just a = shorten (suc i) k (xs ++ (a ∷ [])) eq
