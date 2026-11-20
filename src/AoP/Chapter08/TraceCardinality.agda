{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TraceCardinality where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (suc)

-- Exercise 8.16, trace counting. Match each required query to one
-- occurrence in the actual trace. Remove that occurrence before
-- counting the remaining queries; freshness ensures none is lost.
module Count {A : Set} where
  data Distinct : List A → Set where
    nil : Distinct []
    cons : ∀ {a xs} → (a ∈ xs → ⊥) → Distinct xs → Distinct (a ∷ xs)

  erase : ∀ {a : A} {xs} → a ∈ xs → List A
  erase {xs = _ ∷ xs} here = xs
  erase {xs = x ∷ _} (there m) = x ∷ erase m

  length-law : ∀ {a : A} {xs} (m : a ∈ xs) → suc (len (erase m)) ≡ len xs
  length-law here = refl
  length-law (there m) = cong suc (length-law m)

  retain : ∀ {a b : A} {xs} (m : a ∈ xs) → (a ≡ b → ⊥) → b ∈ xs → b ∈ erase m
  retain here ne here with ne refl
  ... | ()
  retain here ne (there n) = n
  retain (there m) ne here = here
  retain (there m) ne (there n) = there (retain m ne n)

  bound : ∀ {xs ys} → Distinct xs → (∀ a → a ∈ xs → a ∈ ys) → len xs ≤ len ys
  bound nil incl = z≤
  bound {ys = ys} (cons {a} fresh d) incl = cast (length-law hit) (s≤ (bound d rest))
    where hit = incl a here
          rest : ∀ b → _ → b ∈ erase hit
          rest b m = retain hit (λ { refl → fresh m }) (incl b (there m))
          cast : ∀ {i j k} → j ≡ k → i ≤ j → i ≤ k
          cast refl p = p
