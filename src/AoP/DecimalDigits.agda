{-# OPTIONS --safe --without-K #-}
module AoP.DecimalDigits where

open import AoP.Prelude
open import AoP.PositiveFold using (Positive; encode; decode; round-nat)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

-- Exercise 1.16. Numerals are built from the most significant end.
-- The first digit must be nonzero; later digits may be zero. In
-- particular 105 is legal and 0105 has no constructor expression.
data Nonzero : Set where
  one two three four five six seven eight nine : Nonzero

data Digit : Set where
  oh : Digit
  nonzero : Nonzero → Digit

data Digits : Set where
  first : Nonzero → Digits
  append : Digits → Digit → Digits

fold : ∀ {A : Set} → (Nonzero → A) → (A → Digit → A) → Digits → A
fold base step (first d) = base d
fold base step (append ds d) = step (fold base step ds) d

-- PositiveFold.encode counts successor steps *after* one.
index : Nonzero → Nat
index one = 0
index two = 1
index three = 2
index four = 3
index five = 4
index six = 5
index seven = 6
index eight = 7
index nine = 8

value : Digit → Nat
value oh = 0
value (nonzero d) = suc (index d)

scale : Positive → Digit → Positive
scale p d = encode (9 + (decode p * 10 + value d))

eval : Digits → Positive
eval = fold (λ d → encode (index d)) scale

-- On ordinary magnitudes the append step is multiplication by ten
-- followed by addition of the units digit.
magnitude : Positive → Nat
magnitude p = suc (decode p)

shift : ∀ p d → magnitude (scale p d) ≡ 10 + (decode p * 10 + value d)
shift p d = cong suc (round-nat _)

example : magnitude (eval (append (append (first one) oh) (nonzero five))) ≡ 105
example = refl

-- A decimal printer is specified by both inverse laws. The second law
-- demands the original digits, which is why leading zeros were excluded.
record Printer : Set where
  field decimal : Positive → Digits
        reads-back : ∀ p → eval (decimal p) ≡ p
        prints-back : ∀ ds → decimal (eval ds) ≡ ds
