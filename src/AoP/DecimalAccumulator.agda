{-# OPTIONS --safe --without-K #-}
module AoP.DecimalAccumulator where

open import AoP.Prelude
open import AoP.DecimalDigits using (Digit; oh; nonzero; one; five; value)
open import AoP.DecimalDivision using (tens; Split; parts; split)
open import AoP.NatOrder using (_≤_; z≤; s≤; weaken; rid; chain)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Exercise 6.1. The reference recurrence appends each low digit on
-- return. Carrying the suffix instead puts each digit in place once.
-- The expansion index certifies the numerical value of the result;
-- an appended digit always has a positive higher part.
data Expansion : Nat → Set where
  single : (d : Digit) → Expansion (value d)
  more : ∀ {q} → Expansion (suc q) → (d : Digit) → Expansion (tens (suc q) + value d)

private
  pad : ∀ n {a b} → a ≤ b → a ≤ n + b
  pad zero p = p
  pad (suc n) p = weaken (pad n p)
  small : ∀ q d → q ≤ tens q + value d
  small zero d = z≤
  small (suc q) d = s≤ (pad 9 (small q d))

  build : ∀ fuel n → n ≤ fuel → Expansion n
  build zero .0 z≤ = single oh
  build (suc k) n bound with split n
  ... | parts zero d = single d
  ... | parts (suc q) d with bound
  ...   | s≤ h = more (build k (suc q) (chain (s≤ (pad 8 (small q d))) h)) d

reference : ∀ {n} → Expansion n → List Digit
reference (single d) = d ∷ []
reference (more e d) = reference e ++ (d ∷ [])

acc : ∀ {n} → Expansion n → List Digit → List Digit
acc (single d) tail = d ∷ tail
acc (more e d) tail = acc e (d ∷ tail)

private
  append-low : ∀ (xs : List Digit) d ys → (xs ++ (d ∷ [])) ++ ys ≡ xs ++ (d ∷ ys)
  append-low [] d ys = refl
  append-low (x ∷ xs) d ys = cong (x ∷_) (append-low xs d ys)

invariant : ∀ {n} (e : Expansion n) tail → reference e ++ tail ≡ acc e tail
invariant (single d) tail = refl
invariant (more e d) tail = append-low (reference e) d tail ∙ invariant e (d ∷ tail)

print : Nat → List Digit
print n = acc (build n n (rid n)) []

zero-example : print 0 ≡ oh ∷ []
zero-example = refl
internal-zero : print 105 ≡ nonzero one ∷ oh ∷ nonzero five ∷ []
internal-zero = refl
