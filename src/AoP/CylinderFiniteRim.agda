{-# OPTIONS --safe --without-K #-}
module AoP.CylinderFiniteRim where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Cylinder using (module Grid)
open import AoP.CylinderCachedColumn using (module Table)

-- Row n has exactly n indices, starting at the top. Cyclic neighbours
-- are defined for every positive height, including a one-row cylinder
-- on which the three moves lead to the same cell.
data Row : Nat → Set where
  top : ∀ {n} → Row (suc n)
  below : ∀ {n} → Row n → Row (suc n)

last : ∀ n → Row (suc n)
last zero = top
last (suc n) = below (last n)

weaken : ∀ {n} → Row n → Row (suc n)
weaken top = top
weaken (below i) = below (weaken i)

up : ∀ {n} → Row (suc n) → Row (suc n)
up {n} top = last n
up (below i) = weaken i

-- For the last row return top rather than an index past the rim.
open import AoP.Polynomial using (_⊎_; inl; inr)
advance : ∀ {n} → Row n → Row n ⊎ ⊤
advance {suc zero} top = inr tt
advance {suc (suc n)} top = inl (below top)
advance (below i) with advance i
... | inl j = inl (below j)
... | inr _ = inr tt

down : ∀ {n} → Row (suc n) → Row (suc n)
down i with advance i
... | inl j = j
... | inr _ = top

-- Check the boundary equations symbolically at every positive height.
advance-last : ∀ n → advance (last n) ≡ inr tt
advance-last zero = refl
advance-last (suc n) rewrite advance-last n = refl

down-last : ∀ n → down (last n) ≡ top
down-last n rewrite advance-last n = refl

up-top : ∀ n → up top ≡ last n
up-top n = refl

-- Materialize all entries in a dependent tuple. Its tail stores the
-- remaining rows; get returns the certificate indexed by its own row.
Tuple : ∀ n → (Row n → Set) → Set
Tuple zero P = ⊤
Tuple (suc n) P = P top × Tuple n (λ i → P (below i))

pack : ∀ n {P} → (∀ i → P i) → Tuple n P
pack zero f = tt
pack (suc n) f = f top , pack n (λ i → f (below i))

get : ∀ {n} (P : Row n → Set) → Tuple n P → ∀ i → P i
get P xs top = fst xs
get P xs (below i) = get (λ j → P (below j)) (snd xs) i

module Solve (n : Nat) where
  open Grid (Row (suc n)) up down using (Column)
  open Table (Row (suc n)) up down
  Rim : Column → List Column → Set
  Rim c cs = Tuple (suc n) (λ i → Cell c i cs)
  solve : ∀ c cs → Rim c cs
  solve c [] = pack (suc n) (end c)
  solve c (d ∷ ds) = let tail = solve d ds in
    pack (suc n) (λ r → step c r d (get (λ i → Cell d i ds) tail))
