{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.Hyperproduct where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter03.Horner using (module Ruby; tri; map)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Exercise 3.10. In [a,b,c], the factors are a, b², and c⁴: each
-- successive exponent doubles. Evaluate instead as a · (b · c²)².
-- Horner's rule applies because squaring distributes over a product
-- in a commutative monoid. The calculation keeps that proviso explicit.
module Binary {M : Set} (e : M) (_·_ : M → M → M)
              (unit : ∀ a → e · a ≡ a)
              (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
              (comm : ∀ a b → a · b ≡ b · a) where
  private
    back : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
    back refl = refl
  square : M → M
  square x = x · x

  distribute : ∀ a b → square a · square b ≡ square (a · b)
  distribute a b = begin
    (a · a) · (b · b) ≡⟨ assoc a a (b · b) ⟩
    a · (a · (b · b)) ≡⟨ cong (a ·_) (back (assoc a b b)) ⟩
    a · ((a · b) · b) ≡⟨ cong (λ z → a · (z · b)) (comm a b) ⟩
    a · ((b · a) · b) ≡⟨ cong (a ·_) (assoc b a b) ⟩
    a · (b · (a · b)) ≡⟨ back (assoc a b (a · b)) ⟩
    square (a · b) ∎

  module H = Ruby e _·_ square (back (unit e)) distribute

  binary-product : List M → M
  binary-product = ⦅ e ∣ (λ a tail → a · square tail) ⦆

  -- Starting at position i, square each factor i times (exponent 2^i).
  weight : Nat → M → M
  weight zero a = a
  weight (suc i) a = square (weight i a)
  factors : Nat → List M → List M
  factors i [] = []
  factors i (a ∷ xs) = weight i a ∷ factors (suc i) xs
  shift : ∀ i xs → map square (factors i xs) ≡ factors (suc i) xs
  shift i [] = refl
  shift i (a ∷ xs) = cong (weight (suc i) a ∷_) (shift (suc i) xs)
  triangle : ∀ xs → tri square xs ≡ factors zero xs
  triangle [] = refl
  triangle (a ∷ xs) = cong (a ∷_) (cong (map square) (triangle xs) ∙ shift zero xs)

  correct : ∀ xs → H.reduce (factors zero xs) ≡ binary-product xs
  correct xs = cong H.reduce (back (triangle xs)) ∙ H.horner xs
