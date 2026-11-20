{-# OPTIONS --safe --without-K #-}
module AoP.Binary where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.Prelude
open import AoP.Squaring using (Bits; end; _O; _I; value)

-- §§6.1, 6.4: binary numerals. An increment carries through trailing
-- ones. As end denotes zero, its successor consists of a single one.
inc : Bits → Bits
inc end = end I
inc (bs O) = bs I
inc (bs I) = inc bs O

+-suc : ∀ n m → n + suc m ≡ suc (n + m)
+-suc zero m = refl
+-suc (suc n) m = cong suc (+-suc n m)

inc-value : ∀ bs → value (inc bs) ≡ suc (value bs)
inc-value end = refl
inc-value (bs O) = refl
inc-value (bs I) = begin
  value (inc bs) + value (inc bs)
    ≡⟨ cong (λ n → n + n) (inc-value bs) ⟩
  suc (value bs) + suc (value bs)
    ≡⟨ cong suc (+-suc (value bs) (value bs)) ⟩
  suc (value (bs I)) ∎

encode : Nat → Bits
encode zero = end
encode (suc n) = inc (encode n)

-- Constructive surjectivity of evaluation. No inverse law on arbitrary
-- words is possible: end and end O both evaluate to zero.
value-encode : ∀ n → value (encode n) ≡ n
value-encode zero = refl
value-encode (suc n) = begin
  value (inc (encode n))  ≡⟨ inc-value (encode n) ⟩
  suc (value (encode n))  ≡⟨ cong suc (value-encode n) ⟩
  suc n ∎
