{-# OPTIONS --safe --without-K #-}
module AoP.FilledPrefix where

open import AoP.Prelude
open import AoP.FillPrefixes using (Prefix; same; drop; module Restricted)
open import AoP.Detab
open import AoP.EntabLength using (module Bound)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; weaken; sum-mono)
open import AoP.Snoc using (ε; _▻_)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Once filled, a line ends at a stop. Filling it again adds a whole
-- width. Any proper prefix starts shorter and can add at most a width.
module Law {A : Set} (n : Nat) where
  open Expand {A} n
  open Restricted {A} n
  open Bound {A} n using (len)
  private
    pos : ∀ xs → position xs ≤ n
    pos ε = rid n
    pos (xs ▻ newline) = rid n
    pos (xs ▻ c) with c | position xs | pos xs
    ... | blank | 0 | _ = rid n
    ... | tab | 0 | _ = rid n
    ... | glyph _ | 0 | _ = rid n
    ... | blank | suc k | p = chain (weaken (rid k)) p
    ... | tab | suc k | p = chain (weaken (rid k)) p
    ... | glyph _ | suc k | p = chain (weaken (rid k)) p
    ... | newline | _ | _ = rid n
    slide : ∀ k l → k + suc l ≡ suc (k + l)
    slide 0 l = refl
    slide (suc k) l = cong suc (slide k l)
    count : ∀ xs k → len (blanks xs k) ≡ k + len xs
    count xs 0 = refl
    count xs (suc k) = count (xs ▻ blank) k ∙ slide k (len xs)
    prefix-len : ∀ {xs ys : Text} → Prefix xs ys → len xs ≤ len ys
    prefix-len same = rid _
    prefix-len (drop a p) = weaken (prefix-len p)
    cancel : ∀ k {a b} → k + a ≤ k + b → a ≤ b
    cancel 0 p = p
    cancel (suc k) (s≤ p) = cancel k p
    equal : ∀ {xs ys : Text} → Prefix xs ys → len ys ≤ len xs → xs ≡ ys
    equal same _ = refl
    equal (drop a p) le with chain le (prefix-len p)
    ... | bad = impossible bad
      where impossible : ∀ {k} {X : Set} → suc k ≤ k → X
            impossible {0} ()
            impossible {suc k} (s≤ q) = impossible q

  keep : ∀ xs → V (fill xs) (fill xs)
  keep xs = same , refl

  fixed : ∀ xs {y} → V y (fill xs) → y ≡ fill xs
  fixed xs {y} (pr , eq) = equal pr (cancel (suc n) compare)
    where
    lengths : suc (position y) + len y ≡ suc n + len (fill xs)
    lengths with count y (suc (position y)) | count (fill xs) (suc (position (fill xs))) | cong len eq
    ... | l | r | e rewrite reset (position xs) xs refl = sym′ l ∙ e ∙ r
      where sym′ : ∀ {a b : Nat} → a ≡ b → b ≡ a
            sym′ refl = refl
    compare : suc n + len (fill xs) ≤ suc n + len y
    compare with sum-mono (s≤ (pos y)) (rid (len y))
    ... | le rewrite lengths = le
