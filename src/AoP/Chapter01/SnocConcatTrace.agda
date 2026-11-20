{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.SnocConcatTrace where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; _++_; fromSnoc)
open import Agda.Builtin.Nat using (Nat)

-- §1.3. Concatenate [1,2,3] and [4,5]. With rear constructors,
-- inspecting the second argument exposes 5 first. Rebuilding the
-- result appends 4 before 5; the first argument is never inspected.
front : Snoc Nat
front = ε ▻ 1 ▻ 2 ▻ 3

trace : front ++ (ε ▻ 4 ▻ 5) ≡ front ▻ 4 ▻ 5
trace = begin
  front ++ ((ε ▻ 4) ▻ 5) ≡⟨⟩
  (front ++ (ε ▻ 4)) ▻ 5 ≡⟨⟩
  ((front ++ ε) ▻ 4) ▻ 5 ≡⟨⟩
  front ▻ 4 ▻ 5 ∎

read-back : fromSnoc (front ++ (ε ▻ 4 ▻ 5)) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
read-back = cong fromSnoc trace
