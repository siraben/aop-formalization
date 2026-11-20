{-# OPTIONS --safe --without-K #-}
module AoP.DecimalAccumulator where

open import AoP.Prelude
open import AoP.DecimalDigits using (Digit; Nonzero; oh; nonzero; one; five; value)
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

-- Fuse build with acc. The recursive call takes the decimal quotient
-- and the suffix already extended by its low digit. No Expansion is
-- allocated by direct; it appears only on the specification side.
direct : ∀ fuel n → n ≤ fuel → List Digit → List Digit
direct zero .0 z≤ tail = oh ∷ tail
direct (suc k) n bound tail with split n
... | parts zero d = d ∷ tail
... | parts (suc q) d with bound
...   | s≤ h = direct k (suc q) (chain (s≤ (pad 8 (small q d))) h) (d ∷ tail)

fusion : ∀ fuel n (p : n ≤ fuel) tail → acc (build fuel n p) tail ≡ direct fuel n p tail
fusion zero .0 z≤ tail = refl
fusion (suc k) n bound tail with split n
... | parts zero d = refl
... | parts (suc q) d with bound
...   | s≤ h = fusion k (suc q) (chain (s≤ (pad 8 (small q d))) h) (d ∷ tail)

printer : Nat → List Digit
printer n = direct n n (rid n) []

correct : ∀ n → print n ≡ printer n
correct n = fusion n n (rid n) []

-- Reading a digit shifts the accumulated magnitude one decimal place.
-- Reading the generated prefix in front of any suffix therefore leaves
-- exactly the original number as the starting magnitude for that suffix.
read-from : Nat → List Digit → Nat
read-from m [] = m
read-from m (d ∷ ds) = read-from (tens m + value d) ds

read-acc : ∀ {n} (e : Expansion n) tail → read-from 0 (acc e tail) ≡ read-from n tail
read-acc (single d) tail = refl
read-acc (more e d) tail = read-acc e (d ∷ tail)

round-trip : ∀ n → read-from 0 (printer n) ≡ n
round-trip n = cong (read-from 0) (back (correct n)) ∙ read-acc (build n n (rid n)) []
  where back : ∀ {x y : List Digit} → x ≡ y → y ≡ x
        back refl = refl

-- Positive dividends start with a nonzero digit even with an arbitrary
-- pending suffix. The multiple-digit case inherits the first digit of
-- its positive quotient; interior zeroes remain unrestricted.
data StartsPositive : List Digit → Set where
  starts : ∀ d ds → StartsPositive (nonzero d ∷ ds)

positive-acc : ∀ {m n} (e : Expansion m) → m ≡ suc n → ∀ tail → StartsPositive (acc e tail)
positive-acc (single oh) () tail
positive-acc (single (nonzero d)) eq tail = starts d tail
positive-acc (more e d) eq tail = positive-acc e refl (d ∷ tail)

no-leading-zero : ∀ n → StartsPositive (printer (suc n))
no-leading-zero n = move (correct (suc n)) (positive-acc (build _ _ (rid (suc n))) refl [])
  where move : ∀ {xs ys} → xs ≡ ys → StartsPositive xs → StartsPositive ys
        move refl p = p

zero-example : print 0 ≡ oh ∷ []
zero-example = refl
internal-zero : print 105 ≡ nonzero one ∷ oh ∷ nonzero five ∷ []
internal-zero = refl
