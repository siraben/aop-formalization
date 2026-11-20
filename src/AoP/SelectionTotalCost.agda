{-# OPTIONS --safe --without-K #-}
module AoP.SelectionTotalCost where

open import AoP.Prelude
open import AoP.SelectionPairFold using (Pair; select; step)
open import AoP.SelectionPairCost using (counted; exact)
open import AoP.SelectionSort using (length)
open import AoP.NatOrder using (_≤_; s≤; rid; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Each pass makes as many comparisons as there are elements in its
-- remainder. The remainder shrinks by exactly one, even on ties.
step-length : ∀ a p → length (snd (step a p)) ≡ suc (length (snd p))
step-length a (b , xs) with compare a b
... | inl _ = refl
... | inr _ = refl
remainder : ∀ a xs → length (snd (select a xs)) ≡ length xs
remainder a [] = refl
remainder a (b ∷ bs) = step-length a (select b bs) ∙ cong suc (remainder b bs)

tri : Nat → Nat
tri 0 = 0
tri (suc n) = n + tri n

transfer : ∀ {i j k : Nat} → i ≡ j → j ≤ k → i ≤ k
transfer refl le = le
cost : ∀ n xs → length xs ≤ n → Nat
cost n [] le = 0
cost (suc n) (a ∷ xs) (s≤ le) with counted a xs | exact a xs | remainder a xs
... | (k , rs) , c | eq | sz = c + cost n rs (transfer (cong (λ p → length (snd (fst p))) eq ∙ sz) le)

bound : ∀ n xs (le : length xs ≤ n) → cost n xs le ≡ tri (length xs)
bound n [] le = refl
bound (suc n) (a ∷ xs) (s≤ le) with counted a xs | exact a xs | remainder a xs
... | (k , rs) , c | eq | sz = cong (c +_) (bound n rs (transfer size le)) ∙ finish
  where size = cong (λ p → length (snd (fst p))) eq ∙ sz
        finish : c + tri (length rs) ≡ length xs + tri (length xs)
        finish rewrite size | cong snd eq = refl
