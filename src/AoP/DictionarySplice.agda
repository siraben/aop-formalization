{-# OPTIONS --safe --without-K #-}
module AoP.DictionarySplice where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.UniformCodeCost using (module Law)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; rid; sum-mono)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- §9.4. At a table entry the state is the text decoded so far.
-- Any continuation, including an overlapping pointer, sees exactly
-- that text. Replacing its encoding with a cheaper one is safe.
module Splice {A : Set} (c p : Nat) where
  open Text {A}
  price = Law.bits {A} c p
  resume : ∀ xs ps qs {ys} → run xs ps ≡ just ys → run xs (ps ++ qs) ≡ run ys qs
  resume xs [] qs refl = refl
  resume xs (sym a ∷ ps) qs ok = resume (xs ++ (a ∷ [])) ps qs ok
  resume xs (ptr i k ∷ ps) qs ok with copy i (suc k) xs
  ... | just zs = resume zs ps qs ok
  ... | nothing with ok
  ...   | ()
  private
    assoc+ : ∀ a b d → a + (b + d) ≡ (a + b) + d
    assoc+ 0 b d = refl
    assoc+ (suc a) b d = cong suc (assoc+ a b d)
  append-cost : ∀ xs ys → price (xs ++ ys) ≡ price xs + price ys
  append-cost [] ys = refl
  append-cost (sym a ∷ xs) ys rewrite append-cost xs ys = assoc+ c (price xs) (price ys)
  append-cost (ptr i k ∷ xs) ys rewrite append-cost xs ys = assoc+ p (price xs) (price ys)
  cheaper : ∀ ps qs tail → price ps ≤ price qs → price (ps ++ tail) ≤ price (qs ++ tail)
  cheaper ps qs tail le rewrite append-cost ps tail | append-cost qs tail = sum-mono le (rid _)
  replace : ∀ xs ps qs tail {ys} → run xs ps ≡ just ys → run xs qs ≡ just ys → price ps ≤ price qs →
    (run xs (ps ++ tail) ≡ run xs (qs ++ tail)) × (price (ps ++ tail) ≤ price (qs ++ tail))
  replace xs ps qs tail ok ok′ le = (resume xs ps tail ok ∙ reverse (resume xs qs tail ok′)) , cheaper ps qs tail le
    where reverse : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
          reverse refl = refl
