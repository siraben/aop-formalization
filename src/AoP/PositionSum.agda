{-# OPTIONS --safe --without-K #-}
module AoP.PositionSum where

open import AoP.Prelude
open import AoP.Horner using (tri; map; module Ruby)
open import AoP.Folds using (⦅_∣_⦆)
open import AoP.WeightedPaths using (Pair; lift; merge; seed; distribute)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Exercise 3.13. Entry a at position i contributes i*a, starting from
-- zero. Keep its original weight alongside that contribution so that
-- moving it one position right requires only adding a. This is the
-- same shift used when a tip moves one edge deeper in exercise 3.14.
terms : Nat → List Nat → List Pair
terms i [] = []
terms i (a ∷ xs) = (a , i * a) ∷ terms (suc i) xs

shift : ∀ i xs → map lift (terms i xs) ≡ terms (suc i) xs
shift i [] = refl
shift i (a ∷ xs) = cong ((a , suc i * a) ∷_) (shift (suc i) xs)

triangle : ∀ xs → tri lift (map seed xs) ≡ terms 0 xs
triangle [] = refl
triangle (a ∷ xs) = cong (seed a ∷_) (cong (map lift) (triangle xs) ∙ shift 0 xs)

module H = Ruby (0 , 0) merge lift refl distribute

step : Nat → Pair → Pair
step a p = merge (seed a) (lift p)
scan : List Nat → Pair
scan = ⦅ (0 , 0) ∣ step ⦆

private
  inline : ∀ xs → ⦅ (0 , 0) ∣ (λ p q → merge p (lift q)) ⦆ (map seed xs) ≡ scan xs
  inline [] = refl
  inline (a ∷ xs) = cong (step a) (inline xs)
  back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  back refl = refl

correct : ∀ xs → H.reduce (terms 0 xs) ≡ scan xs
correct xs = begin
  H.reduce (terms 0 xs) ≡⟨ cong H.reduce (back (triangle xs)) ⟩
  H.reduce (tri lift (map seed xs)) ≡⟨ H.horner (map seed xs) ⟩
  ⦅ (0 , 0) ∣ (λ p q → merge p (lift q)) ⦆ (map seed xs) ≡⟨ inline xs ⟩
  scan xs ∎

-- Sum 2+3+5 = 10; weighted sum 0*2 + 1*3 + 2*5 = 13.
example : scan (2 ∷ 3 ∷ 5 ∷ []) ≡ (10 , 13)
example = begin
  scan (2 ∷ 3 ∷ 5 ∷ []) ≡⟨⟩
  step 2 (step 3 (5 , 0)) ≡⟨⟩
  step 2 (8 , 5) ≡⟨⟩
  merge (seed 2) (lift (8 , 5)) ≡⟨⟩
  merge (2 , 0) (8 , 13) ≡⟨⟩
  (10 , 13) ∎

-- Start instead from the explicit weighted terms. The correctness
-- theorem takes their reduction to the same cached computation.
explicit : H.reduce ((2 , 0) ∷ (3 , 3) ∷ (5 , 10) ∷ []) ≡ (10 , 13)
explicit = correct (2 ∷ 3 ∷ 5 ∷ []) ∙ example
