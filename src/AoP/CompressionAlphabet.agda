{-# OPTIONS --safe --without-K #-}
module AoP.CompressionAlphabet where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.Subsequences using (_∈_; here; merge)
open import AoP.Naturality using (_++_)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.Maybe using (just; nothing)

-- §9.4. The alphabet of possible literals can be read from the target,
-- even if the underlying character type is infinite. Decoding never
-- erases a character: every literal remains in the final output. This
-- gives the finite literal dictionary used in exhaustive encoder search.
module Letters {A : Set} where
  open Text {A}

  kept-copy : ∀ i k xs {ys a} → copy i k xs ≡ just ys → a ∈ xs → a ∈ ys
  kept-copy i zero xs refl m = m
  kept-copy i (suc k) xs eq m with lookup i xs
  ... | nothing with eq
  ...   | ()
  kept-copy i (suc k) xs eq m | just x = kept-copy (suc i) k (xs ++ (x ∷ [])) eq (merge xs (x ∷ []) (inl m))

  kept : ∀ ops xs {ys a} → run xs ops ≡ just ys → a ∈ xs → a ∈ ys
  kept [] xs refl m = m
  kept (sym x ∷ ops) xs eq m = kept ops _ eq (merge xs (x ∷ []) (inl m))
  kept (ptr i k ∷ ops) xs eq m with copy i (suc k) xs in cp
  ... | nothing with eq
  ...   | ()
  kept (ptr i k ∷ ops) xs eq m | just zs = kept ops zs eq (kept-copy i (suc k) xs cp m)

  data Uses (ys : List A) : List Code → Set where
    end : Uses ys []
    literal : ∀ {a ops} → a ∈ ys → Uses ys ops → Uses ys (sym a ∷ ops)
    pointer : ∀ {i k ops} → Uses ys ops → Uses ys (ptr i k ∷ ops)

  alphabet : ∀ ops xs {ys} → run xs ops ≡ just ys → Uses ys ops
  alphabet [] xs eq = end
  alphabet (sym a ∷ ops) xs eq = literal (kept ops _ eq (merge xs (a ∷ []) (inr here))) (alphabet ops _ eq)
  alphabet (ptr i k ∷ ops) xs eq with copy i (suc k) xs
  ... | just zs = pointer (alphabet ops zs eq)
  ... | nothing with eq
  ...   | ()
