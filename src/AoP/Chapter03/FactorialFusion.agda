{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.FactorialFusion where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturals using (foldn; foldn-unique; factorials)
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter03.Predecessors using (preds; state; step; invariant)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Exercise 3.7. For 4!, the specification constructs [4,3,2,1] and
-- multiplies its elements. Fuse that multiplication into the index-
-- carrying fold of exercise 3.6: the accumulator now contains just the
-- current index and its product, the same pair used for factorial in §1.2.
product : List Nat → Nat
product = ⦅ 1 ∣ _*_ ⦆

reduce : List Nat × Nat → Nat × Nat
reduce (xs , n) = n , product xs

advance : Nat × Nat → Nat × Nat
advance (n , acc) = suc n , suc n * acc

commute : ∀ p → reduce (step p) ≡ advance (reduce p)
commute (xs , n) = refl

fused : ∀ n → reduce (state n) ≡ factorials n
fused = foldn-unique (λ n → reduce (state n)) (0 , 1) advance refl (λ n → commute (state n))

correct : ∀ n → product (preds n) ≡ snd (factorials n)
correct n = begin
  product (preds n)      ≡⟨ back (cong (λ p → product (fst p)) (invariant n)) ⟩
  snd (reduce (state n)) ≡⟨ cong snd (fused n) ⟩
  snd (factorials n) ∎
  where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
        back refl = refl

-- At the final successor step for 4!, the list-producing fold would
-- prepend 4. The commuting square replaces that allocation followed
-- by multiplication with an update of the cached pair (3,6).
four-step : reduce (state 4) ≡ (4 , 24)
four-step = begin
  reduce (state 4) ≡⟨⟩
  reduce (step (state 3)) ≡⟨ commute (state 3) ⟩
  advance (reduce (state 3)) ≡⟨ cong advance (fused 3) ⟩
  advance (factorials 3) ≡⟨⟩
  advance (3 , 6) ≡⟨⟩
  (4 , 4 * 6) ≡⟨⟩
  (4 , 24) ∎
