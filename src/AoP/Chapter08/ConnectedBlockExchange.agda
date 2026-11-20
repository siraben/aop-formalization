{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedBlockExchange where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter07.LongestPrefix using (module Prefix)
open import AoP.Chapter05.Subsequences using (there)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exchange a competitor's first block for the longest connected
-- prefix. Extra letters consumed at the front can only remove blocks
-- or shorten the first surviving block. Neither costs another block.
module Exchange {A : Set} (Q : A → A → Set) where
  open Law Q
  open Prefix {A}
  data Within : Nat → List A → Set where
    empty : ∀ {n} → Within n []
    cut : ∀ {n a xs ys} → Connected (a ∷ xs) → Within n ys → Within (suc n) (a ∷ (xs ++ ys))
  weaken : ∀ {n xs} → Within n xs → Within (suc n) xs
  weaken empty = empty
  weaken (cut c w) = cut c (weaken w)
  drop : ∀ {n x xs} → Within n (x ∷ xs) → Within n xs
  drop (cut {xs = []} c w) = weaken w
  drop (cut {xs = _ ∷ _} c w) = cut (λ a b m k → c a b (there m) (there k)) w
  trim : ∀ xs {ys n} → Within n (xs ++ ys) → Within n ys
  trim [] w = w
  trim (x ∷ xs) w = trim xs (drop w)
  prefix : ∀ xs ys → xs ≼ (xs ++ ys)
  prefix [] ys = nil
  prefix (x ∷ xs) ys = cons (prefix xs ys)
  cancel : ∀ {xs ys} → xs ≼ ys → ∀ {r s n} → xs ++ r ≡ ys ++ s → Within n r → Within n s
  cancel (nil {ys}) refl w = trim ys w
  cancel (cons p) eq w = cancel p (tails eq) w
    where tails : ∀ {a b : A} {u v} → a ∷ u ≡ b ∷ v → u ≡ v
          tails refl = refl
  exchange : ∀ {a xs n} (g : Longest Connected (a ∷ xs)) → Within (suc n) (a ∷ xs) → Within n (Longest.rest g)
  exchange (result b s eq c longest) (cut {a = a} {xs = xs} {ys = ys} ok tail) = cancel (longest (prefix (a ∷ xs) ys) ok) (rev eq) tail
    where rev : ∀ {X : Set} {u v : X} → u ≡ v → v ≡ u
          rev refl = refl
