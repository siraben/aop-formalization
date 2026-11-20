{-# OPTIONS --safe --without-K #-}
module AoP.BinaryOctal where

open import AoP.Prelude
open import AoP.Folds
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Exercise 6.9. Read a binary word least significant bit first. Unfold
-- it into triples, padding the most significant group with zero bits.
-- Fold the resulting list to octal digits. For example, 110101₂ is
-- 65₈: the two groups read from the low end denote 5 and then 6.
Triple = Bool × (Bool × Bool)
chunks : List Bool → List Triple
chunks [] = []
chunks (a ∷ []) = (a , false , false) ∷ []
chunks (a ∷ b ∷ []) = (a , b , false) ∷ []
chunks (a ∷ b ∷ c ∷ bs) = (a , b , c) ∷ chunks bs

data Oct : Set where
  d0 d1 d2 d3 d4 d5 d6 d7 : Oct

digit : Triple → Oct
digit (false , false , false) = d0
digit (true , false , false) = d1
digit (false , true , false) = d2
digit (true , true , false) = d3
digit (false , false , true) = d4
digit (true , false , true) = d5
digit (false , true , true) = d6
digit (true , true , true) = d7

convert : List Bool → List Oct
convert bs = ⦅ [] ∣ (λ t ds → digit t ∷ ds) ⦆ (chunks bs)

bit : Bool → Nat → Nat
bit false n = n + n
bit true n = 1 + (n + n)
bin = ⦅ 0 ∣ bit ⦆

place : Oct → Nat → Nat
place d n = value d + eight n
  where
  value : Oct → Nat
  value d0 = 0
  value d1 = 1
  value d2 = 2
  value d3 = 3
  value d4 = 4
  value d5 = 5
  value d6 = 6
  value d7 = 7
  eight : Nat → Nat
  eight x = bit false (bit false (bit false x))

private
  slide : ∀ n m → n + suc m ≡ suc (n + m)
  slide zero m = refl
  slide (suc n) m = cong suc (slide n m)
  twice : ∀ n → bit false (suc n) ≡ suc (suc (bit false n))
  twice n = cong suc (slide n n)

  four : ∀ n → bit false (bit false (bit true n)) ≡ place d4 n
  four n = let m = bit false (bit false n) in
    cong (bit false) (twice (bit false n)) ∙ twice (suc m) ∙ cong (λ k → suc (suc k)) (twice m)
  six : ∀ n → bit false (bit true (bit true n)) ≡ place d6 n
  six n = twice (bit false (bit true n)) ∙ cong (λ k → suc (suc k)) (four n)

  group : ∀ a b c n → bit a (bit b (bit c n)) ≡ place (digit (a , b , c)) n
  group false false false n = refl
  group true false false n = refl
  group false true false n = twice _
  group true true false n = cong suc (twice _)
  group false false true n = four n
  group true false true n = cong suc (four n)
  group false true true n = six n
  group true true true n = cong suc (six n)

correct : ∀ bs → bin bs ≡ ⦅ 0 ∣ place ⦆ (convert bs)
correct [] = refl
correct (a ∷ []) = group a false false 0
correct (a ∷ b ∷ []) = group a b false 0
correct (a ∷ b ∷ c ∷ bs) = group a b c (bin bs) ∙ cong (place (digit (a , b , c))) (correct bs)

example : convert (true ∷ false ∷ true ∷ false ∷ true ∷ true ∷ []) ≡ d5 ∷ d6 ∷ []
example = refl
example-value : ⦅ 0 ∣ place ⦆ (d5 ∷ d6 ∷ []) ≡ 53
example-value = refl
