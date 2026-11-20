{-# OPTIONS --safe --without-K #-}
module AoP.OrderedPivot where

open import AoP.Prelude
open import AoP.OrderedMeet using (module Order)
open import AoP.Subsequences using (_∈_; here; there; split; merge)
open import AoP.Polynomial using (inl; inr)
open import AoP.Naturality using (_++_)
open import AoP.Relations using (_←_)

-- §6.6, the pivot step of ordered · flatten = flatten · inordered.
-- Transitivity is exactly what lets a left key and a right key compare
-- via the pivot. Recovering the pivot bounds needs no such assumption.
module Join {A : Set} (R : A ← A) (trans : ∀ {x y z} → R x y → R y z → R x z) where
  open Order {A} using (Ordered; cons; nil)
  record Parts (l : List A) (p : A) (r : List A) : Set where
    constructor parts
    field
      ls : Ordered R l
      before : ∀ {x} → x ∈ l → R x p
      after : ∀ {x} → x ∈ r → R p x
      rs : Ordered R r

  join : ∀ l p r → Parts l p r → Ordered R (l ++ (p ∷ r))
  join [] p r (parts nil _ after rs) = cons after rs
  join (x ∷ xs) p r (parts (cons lb ls) before after rs) = cons bound
    (join xs p r (parts ls (λ m → before (there m)) after rs))
    where
    bound : ∀ {a} → a ∈ (xs ++ (p ∷ r)) → R x a
    bound m with split xs (p ∷ r) m
    ... | inl k = lb k
    ... | inr here = before here
    ... | inr (there k) = trans (before here) (after k)

  separate : ∀ l p r → Ordered R (l ++ (p ∷ r)) → Parts l p r
  separate [] p r (cons lb rs) = parts nil (λ ()) lb rs
  separate (x ∷ xs) p r (cons lb rest) with separate xs p r rest
  ... | parts ls before after rs = parts (cons (λ m → lb (merge xs _ (inl m))) ls)
    (λ { here → lb (merge xs _ (inr here)) ; (there m) → before m }) after rs
