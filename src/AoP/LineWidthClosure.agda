{-# OPTIONS --safe --without-K #-}
module AoP.LineWidthClosure where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; chain; rid; weaken; sum-mono; z≤; s≤)
open import AoP.Paragraph using (module Layout)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.56. Removing words from either end removes nonnegative
-- word lengths and their separating spaces. Work with nonempty lines:
-- every prefix has a first word and every suffix has a first word.
module Law {W : Set} (size : W → Nat) (margin : Nat) where
  open Layout size margin
  private
    room : ∀ a b → a ≤ a + b
    room 0 b = z≤
    room (suc a) b = s≤ (room a b)
  prefix-width : ∀ w xs ys → widthFrom w xs ≤ widthFrom w (xs ++ ys)
  prefix-width w [] [] = rid _
  prefix-width w [] (v ∷ vs) = weaken (room (size w) _)
  prefix-width w (v ∷ vs) ys = s≤ (sum-mono (rid _) (prefix-width v vs ys))

  private
    pad : ∀ n m → m ≤ n + m
    pad 0 m = rid m
    pad (suc n) m = weaken (pad n m)

  private
    first : List W → W → W
    first [] w = w
    first (u ∷ us) w = u
    rest : List W → W → List W → List W
    rest [] w xs = xs
    rest (_ ∷ us) w xs = us ++ (w ∷ xs)
  suffix-width : ∀ pre w xs → widthFrom w xs ≤ widthFrom (first pre w) (rest pre w xs)
  suffix-width [] w xs = rid _
  suffix-width (u ∷ []) w xs = weaken (pad (size u) _)
  suffix-width (u ∷ v ∷ vs) w xs = chain (suffix-width (v ∷ vs) w xs) (weaken (pad (size u) _))
