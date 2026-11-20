{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.DecimalSuccessor where

open import AoP.Common.Prelude
open import AoP.Chapter01.DecimalDigits
open import AoP.Chapter01.PositiveFold using (Positive; one; next; encode; decode; round-positive; round-nat)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 1.16. Print by counting from one. Increment only the units
-- place unless it is nine; then emit zero and propagate a carry. A
-- leading nine becomes ten, which introduces one extra digit.
bump : Nonzero → Digits
bump one = first two
bump two = first three
bump three = first four
bump four = first five
bump five = first six
bump six = first seven
bump seven = first eight
bump eight = first nine
bump nine = append (first one) oh

inc : Digits → Digits
inc (first d) = bump d
inc (append ds oh) = append ds (nonzero one)
inc (append ds (nonzero one)) = append ds (nonzero two)
inc (append ds (nonzero two)) = append ds (nonzero three)
inc (append ds (nonzero three)) = append ds (nonzero four)
inc (append ds (nonzero four)) = append ds (nonzero five)
inc (append ds (nonzero five)) = append ds (nonzero six)
inc (append ds (nonzero six)) = append ds (nonzero seven)
inc (append ds (nonzero seven)) = append ds (nonzero eight)
inc (append ds (nonzero eight)) = append ds (nonzero nine)
inc (append ds (nonzero nine)) = append (inc ds) oh

print : Positive → Digits
print one = first one
print (next p) = inc (print p)

private
  tail-suc : ∀ a b → a + suc b ≡ suc (a + b)
  tail-suc Agda.Builtin.Nat.zero b = refl
  tail-suc (suc a) b = cong suc (tail-suc a b)

  step : ∀ p d e → value e ≡ suc (value d) → scale p e ≡ next (scale p d)
  step p d e eq = cong (λ n → encode (9 + n)) (cong (k +_) eq ∙ tail-suc k (value d))
    where k = decode p * 10

  carry : ∀ p → scale (next p) oh ≡ next (scale p (nonzero nine))
  carry p = cong (λ n → encode (10 + n)) (slide 9 (decode p * 10))
    where
    slide : ∀ n k → n + (k + 0) ≡ k + n
    slide Agda.Builtin.Nat.zero k = refl
    slide (suc n) k = cong suc (slide n k) ∙ back (tail-suc k n)
      where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
            back refl = refl

bump-law : ∀ d → eval (bump d) ≡ next (eval (first d))
bump-law one = refl
bump-law two = refl
bump-law three = refl
bump-law four = refl
bump-law five = refl
bump-law six = refl
bump-law seven = refl
bump-law eight = refl
bump-law nine = refl

inc-law : ∀ ds → eval (inc ds) ≡ next (eval ds)
inc-law (first d) = bump-law d
inc-law (append ds oh) = step (eval ds) oh (nonzero one) refl
inc-law (append ds (nonzero one)) = step (eval ds) (nonzero one) (nonzero two) refl
inc-law (append ds (nonzero two)) = step (eval ds) (nonzero two) (nonzero three) refl
inc-law (append ds (nonzero three)) = step (eval ds) (nonzero three) (nonzero four) refl
inc-law (append ds (nonzero four)) = step (eval ds) (nonzero four) (nonzero five) refl
inc-law (append ds (nonzero five)) = step (eval ds) (nonzero five) (nonzero six) refl
inc-law (append ds (nonzero six)) = step (eval ds) (nonzero six) (nonzero seven) refl
inc-law (append ds (nonzero seven)) = step (eval ds) (nonzero seven) (nonzero eight) refl
inc-law (append ds (nonzero eight)) = step (eval ds) (nonzero eight) (nonzero nine) refl
inc-law (append ds (nonzero nine)) rewrite inc-law ds = carry (eval ds)

reads : ∀ p → eval (print p) ≡ p
reads one = refl
reads (next p) = inc-law (print p) ∙ cong next (reads p)
