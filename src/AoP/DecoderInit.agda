{-# OPTIONS --safe --without-K #-}
module AoP.DecoderInit where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.ShortenPointer using (module Law)
open import AoP.UniformCodeCost using () renaming (module Law to Charges)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; z≤; rid; sum-mono)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; suc)

module Init {A : Set} (c p : Nat) where
  open Text {A}
  open Law {A}
  open Charges {A} using (bits)
  price = bits c p

  Result : List A → List Code → List A → Set
  Result xs ops ys = Σ (List Code) λ qs → Σ (List A) λ zs → Σ A λ a →
    (run xs qs ≡ just zs) × (ys ≡ (zs ++ (a ∷ []))) × (price qs ≤ price ops)

  -- Keep all instructions before the last. A final literal or
  -- one-letter pointer disappears; any longer pointer keeps its price.
  trim : ∀ xs op ops {ys} → run xs (op ∷ ops) ≡ just ys → Result xs (op ∷ ops) ys
  trim xs (sym a) [] refl = [] , xs , a , refl , refl , z≤
  trim xs (ptr i k) [] eq with copy i (suc k) xs in copied
  ... | nothing with eq
  ...   | ()
  trim xs (ptr i k) [] refl | just ys with shorten i k xs copied
  ... | zs , a , shorter , split with k
  ...   | 0 with shorter
  ...     | refl = [] , xs , a , refl , split , z≤
  trim xs (ptr i k) [] refl | just ys | zs , a , shorter , split | suc j = (ptr i j ∷ []) , zs , a , good , split , rid _
    where good : run xs (ptr i j ∷ []) ≡ just zs
          good rewrite shorter = refl
  trim xs (sym a) (u ∷ us) eq with trim (xs ++ (a ∷ [])) u us eq
  ... | qs , zs , b , ok , split , le = (sym a ∷ qs) , zs , b , ok , split , sum-mono (rid c) le
  trim xs (ptr i k) (u ∷ us) eq with copy i (suc k) xs in copied
  ... | nothing with eq
  ...   | ()
  trim xs (ptr i k) (u ∷ us) eq | just ws with trim ws u us eq
  ... | qs , zs , a , ok , split , le = (ptr i k ∷ qs) , zs , a , good , split , sum-mono (rid p) le
    where good : run xs (ptr i k ∷ qs) ≡ just zs
          good rewrite copied = ok
