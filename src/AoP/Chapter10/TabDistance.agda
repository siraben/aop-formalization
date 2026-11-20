{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TabDistance where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)
open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter10.Detab
open import AoP.Chapter10.Entab
open import AoP.Chapter10.EntabPending
open import AoP.Chapter10.TabFree
open import AoP.Chapter01.Snoc using (_▻_)

-- §10.2. If two blanks are pending one column before a stop, the
-- committed prefix was three columns before it. Relate the encoder's
-- two views: actual distance in the expanded text, and distance at the
-- committed prefix minus pending spaces. `position` stores distance − 1.
module Distance {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n
  open Stops {A} n
  open Image {A} n

  within : ∀ xs k → k ≤ position xs → position (blanks xs k) ≡ position xs - k
  within xs zero le = refl
  within xs (suc k) le with position xs in eq
  ... | suc j with le
  ...   | s≤ small = go (xs ▻ blank) j (cong advance eq) small
    where
    go : ∀ ys j → position ys ≡ j → k ≤ j → position (blanks ys k) ≡ j - k
    go ys .(position ys) refl bound = within ys k bound

  distance : ∀ {s} (p : Plain s) → let b = encode p in
             position s ≡ position (detab (Buffer.code b)) - Buffer.pending b
  distance p with encode p | bounded p
  ... | buf xs k refl | le = within (detab xs) k le
