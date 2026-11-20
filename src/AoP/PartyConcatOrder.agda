{-# OPTIONS --safe --without-K #-}
module AoP.PartyConcatOrder where

open import AoP.Prelude
open import AoP.ListMeet using (Align; nil; cons)
open import AoP.Naturality using (_++_; concat)
open import AoP.NatOrder using (_≤_; z≤; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Exercise 7.43. Comparing guest lists by the sum of natural ratings
-- forgets their lengths: replacing one very popular guest by several
-- equally convivial guests is allowed. Only the list of direct reports
-- is aligned. Flattening their lists preserves improvement.
module Law {Employee : Set} (rating : Employee → Nat) where
  score : List Employee → Nat
  score [] = 0
  score (e ∷ es) = rating e + score es
  R : List Employee → List Employee → Set
  R better worse = score worse ≤ score better

  prepend : ∀ e {xs ys} → R ys xs → R (e ∷ ys) (e ∷ xs)
  prepend e = sum-mono (rid (rating e))

  private
    assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
    assoc 0 b c = refl
    assoc (Agda.Builtin.Nat.suc a) b c = cong Agda.Builtin.Nat.suc (assoc a b c)
  append-score : ∀ xs ys → score (xs ++ ys) ≡ score xs + score ys
  append-score [] ys = refl
  append-score (e ∷ xs) ys = cong (rating e +_) (append-score xs ys) ∙ assoc (rating e) (score xs) (score ys)

  append : ∀ {a b c d} → R b a → R d c → R (b ++ d) (a ++ c)
  append {a} {b} {c} {d} r s rewrite append-score a c | append-score b d = sum-mono r s
  flatten : ∀ {xss yss} → Align R yss xss → R (concat yss) (concat xss)
  flatten nil = z≤
  flatten (cons {b = b} {a} {bs} {as} r rs) = append {a} {b} {concat as} {concat bs} r (flatten rs)
