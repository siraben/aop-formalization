{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanTrimming where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter07.LongestPrefix using (module Prefix)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. After taking a longer first block, the remaining work is a
-- suffix of the competitor's remaining work. Trim the skipped operations
-- from its schedule. Whole blocks may disappear; a partially used block
-- can start at its old intermediate balance. No new block is needed.
module Trim (cap : Nat) where
  open Bank cap

  -- An upper bound on the block count makes the lemma compositional:
  -- the same budget is available after dropping any number of operations.
  data Within : Nat → List Tx → Set where
    done : ∀ {n} → Within n []
    block : ∀ {n t ts rest} → Secure (t ∷ ts) → Within n rest →
            Within (suc n) (t ∷ (ts ++ rest))

  more : ∀ {xs n} → Within n xs → Within (suc n) xs
  more done = done
  more (block secure p) = block secure (more p)

  drop-one : ∀ {t ts n} → Within n (t ∷ ts) → Within n ts
  drop-one (block {ts = []} _ p) = more p
  drop-one (block {ts = x ∷ xs} (_ , c , post _ _ run) p) = block (_ , c , run) p

  drop-prefix : ∀ xs {ys n} → Within n (xs ++ ys) → Within n ys
  drop-prefix [] p = p
  drop-prefix (_ ∷ xs) p = drop-prefix xs (drop-one p)

  open Prefix {Tx}
  prefix : ∀ xs ys → xs ≼ (xs ++ ys)
  prefix [] ys = nil
  prefix (_ ∷ xs) ys = cons (prefix xs ys)

  -- If short is a prefix of long, cancelling their common transactions
  -- leaves the longer block's suffix within the shorter block's budget.
  cancel : ∀ {short long} → short ≼ long → ∀ {r s n} →
           short ++ r ≡ long ++ s → Within n r → Within n s
  cancel (nil {xs}) refl p = drop-prefix xs p
  cancel (cons pref) eq p = cancel pref (tail-eq eq) p
    where tail-eq : ∀ {x y : Tx} {xs ys} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
          tail-eq refl = refl

  exchange : ∀ {t ts n} (g : Longest Secure (t ∷ ts)) →
             Within (suc n) (t ∷ ts) → Within n (Longest.rest g)
  exchange (result long s eq fits dom) (block {t = t} {ts = ts} {rest = r} sec p) =
    cancel (dom (prefix (t ∷ ts) r) sec) (back eq) p
    where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
          back refl = refl
