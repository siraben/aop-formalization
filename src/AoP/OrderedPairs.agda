{-# OPTIONS --safe --without-K #-}
module AoP.OrderedPairs where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import AoP.ConversionCost using (len)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

-- Exercise 8.16. Adding a new input to n old ones introduces n
-- outgoing and n incoming ordered queries. No self-query is added.
pairs : ∀ {A : Set} → List A → List (A × A)
pairs [] = []
pairs (x ∷ xs) = map (x ,_) xs ++ (map (_, x) xs ++ pairs xs)

private
  mapped : ∀ {A B : Set} (f : A → B) xs → len (map f xs) ≡ len xs
  mapped f [] = refl
  mapped f (x ∷ xs) = cong suc (mapped f xs)
  appended : ∀ {A : Set} (xs ys : List A) → len (xs ++ ys) ≡ len xs + len ys
  appended [] ys = refl
  appended (x ∷ xs) ys = cong suc (appended xs ys)
  slide : ∀ n m → n + suc m ≡ suc (n + m)
  slide zero m = refl
  slide (suc n) m = cong suc (slide n m)
  grow : ∀ n k → n + (n * k) ≡ n * suc k
  grow zero k = refl
  grow (suc n) k = cong suc (swap n k (n * k) ∙ cong (k +_) (grow n k))
    where
    swap : ∀ a b c → a + (b + c) ≡ b + (a + c)
    swap zero b c = refl
    swap (suc a) b c rewrite slide b (a + c) = cong suc (swap a b c)

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

count : ∀ {A : Set} (xs : List A) → len (pairs xs) ≡ len xs * pred (len xs)
count [] = refl
count (x ∷ xs) rewrite appended (map (x ,_) xs) (map (_, x) xs ++ pairs xs)
                     | appended (map (_, x) xs) (pairs xs)
                     | mapped (x ,_) xs | mapped (_, x) xs | count xs = cong (len xs +_) (square (len xs))
  where square : ∀ n → n + n * pred n ≡ n * n
        square zero = refl
        square (suc n) = grow (suc n) n
