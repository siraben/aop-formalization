{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.TipTraversal where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; foldt)
open import AoP.Chapter01.Naturality using (_++_)
private variable A : Set

-- §3.5. List the labels at the tips from left to right. Appending
-- child lists can repeatedly copy the same left prefix. Instead fold
-- into functions that put the tips before an arbitrary suffix. At a
-- fork, associativity makes the combining operation function composition.
tips : Tree A → List A
tips = foldt (λ a → a ∷ []) _++_

tipcat : Tree A → List A → List A
tipcat = foldt _∷_ (λ left right suffix → left (right suffix))

private
  assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)
  unit : (xs : List A) → xs ≡ xs ++ []
  unit [] = refl
  unit (x ∷ xs) = cong (x ∷_) (unit xs)

invariant : (t : Tree A) (suffix : List A) → tips t ++ suffix ≡ tipcat t suffix
invariant (tip a) suffix = refl
invariant (bin l r) suffix = begin
  (tips l ++ tips r) ++ suffix ≡⟨ assoc (tips l) (tips r) suffix ⟩
  tips l ++ (tips r ++ suffix) ≡⟨ invariant l (tips r ++ suffix) ⟩
  tipcat l (tips r ++ suffix) ≡⟨ cong (tipcat l) (invariant r suffix) ⟩
  tipcat (bin l r) suffix ∎

correct : (t : Tree A) → tips t ≡ tipcat t []
correct t = unit (tips t) ∙ invariant t []

example : tipcat (bin (bin (tip 1) (tip 2)) (tip 3)) (4 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
example = refl
