{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ReserveClipping where

open import AoP.Common.Prelude
open import AoP.Chapter07.SignedSegment using (up; down; repeat)
open import Agda.Builtin.Nat using (Nat; suc; _-_)
open import Agda.Builtin.Int using (Int; pos; negsuc)

-- Exercise 7.55. Clipping at zero turns motion toward the other side
-- of zero into truncated subtraction. A deposit reduces the stock
-- required by a negative floor; a withdrawal reduces the headroom
-- required by a positive ceiling. Crossings through zero are allowed.
stock space : Int → Nat
stock (pos _) = 0
stock (negsuc n) = suc n
space (pos n) = n
space (negsuc _) = 0

private
  pred : Nat → Nat
  pred 0 = 0
  pred (suc n) = n
  sub-step : ∀ n k → pred (n - k) ≡ n - suc k
  sub-step 0 0 = refl
  sub-step 0 (suc k) = refl
  sub-step (suc n) 0 = refl
  sub-step (suc n) (suc k) = sub-step n k
  credit : ∀ x → stock (up x) ≡ pred (stock x)
  credit (pos _) = refl
  credit (negsuc 0) = refl
  credit (negsuc (suc n)) = refl
  debit : ∀ x → space (down x) ≡ pred (space x)
  debit (pos 0) = refl
  debit (pos (suc n)) = refl
  debit (negsuc _) = refl

release-stock : ∀ k x → stock (repeat k up x) ≡ stock x - k
release-stock 0 x = refl
release-stock (suc k) x = credit (repeat k up x) ∙ cong pred (release-stock k x) ∙ sub-step (stock x) k
release-space : ∀ k x → space (repeat k down x) ≡ space x - k
release-space 0 x = refl
release-space (suc k) x = debit (repeat k down x) ∙ cong pred (release-space k x) ∙ sub-step (space x) k
