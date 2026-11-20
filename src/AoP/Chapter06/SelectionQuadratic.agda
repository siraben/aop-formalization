{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionQuadratic where

open import AoP.Common.Prelude
open import AoP.Chapter06.SelectionTotalCost using (tri; cost; bound)
open import AoP.Chapter06.SelectionSort using (length)
open import AoP.Chapter08.OrderedPairs using (pred)
open import AoP.Common.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Double the triangular count to express the usual closed form
-- without a division operation (including lengths zero and one).
private
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc 0 b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)
  slide : ∀ a b → a + suc b ≡ suc (a + b)
  slide 0 b = refl
  slide (suc a) b = cong suc (slide a b)
  swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
  swap 0 b c = refl
  swap (suc a) b c rewrite slide b (a + c) = cong suc (swap a b c)
  grow : ∀ a b → a + a * b ≡ a * suc b
  grow 0 b = refl
  grow (suc a) b = cong suc (swap a b (a * b) ∙ cong (b +_) (grow a b))
  square : ∀ n → n + n * pred n ≡ n * n
  square 0 = refl
  square (suc n) = grow (suc n) n

double : ∀ n → tri n + tri n ≡ n * pred n
double 0 = refl
double (suc n) = begin
  (n + tri n) + (n + tri n) ≡⟨ assoc n (tri n) (n + tri n) ⟩
  n + (tri n + (n + tri n)) ≡⟨ cong (n +_) (swap (tri n) n (tri n)) ⟩
  n + (n + (tri n + tri n)) ≡⟨ cong (λ x → n + (n + x)) (double n) ⟩
  n + (n + n * pred n) ≡⟨ cong (n +_) (square n) ⟩
  suc n * n ∎

exact : ∀ n xs (p : length xs ≤ n) → cost n xs p + cost n xs p ≡ length xs * pred (length xs)
exact n xs p rewrite bound n xs p = double (length xs)
