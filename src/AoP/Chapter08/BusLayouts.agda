{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BusLayouts where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image; preimage; split; merge)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)

-- Choose k distinct stops among m consecutive blocks starting at j.
-- Skipping moves to the next block with the same quota; taking moves
-- to the same next block with one fewer stop still to place.
data Layout (j : Nat) : Nat → Nat → List Nat → Set where
  done : ∀ {m} → Layout j m 0 []
  skip : ∀ {m k xs} → Layout (suc j) m (suc k) xs → Layout j (suc m) (suc k) xs
  take : ∀ {m k xs} → Layout (suc j) m k xs → Layout j (suc m) (suc k) (j ∷ xs)

layouts : Nat → Nat → Nat → List (List Nat)
layouts j m 0 = [] ∷ []
layouts j 0 (suc k) = []
layouts j (suc m) (suc k) = map (j ∷_) (layouts (suc j) m k) ++ layouts (suc j) m (suc k)

complete : ∀ {j m k xs} → Layout j m k xs → xs ∈ layouts j m k
complete done = here
complete {j} (skip {m} {k} p) = merge (map (j ∷_) (layouts (suc j) m k)) (layouts (suc j) m (suc k)) (inr (complete p))
complete {j} (take {m} {k} p) = merge (map (j ∷_) (layouts (suc j) m k)) (layouts (suc j) m (suc k)) (inl (image (_ ∷_) (complete p)))

sound : ∀ j m k {xs} → xs ∈ layouts j m k → Layout j m k xs
sound j m 0 here = done
sound j m 0 (there ())
sound j (suc m) (suc k) p with split (map (j ∷_) (layouts (suc j) m k)) (layouts (suc j) m (suc k)) p
... | inr q = skip (sound _ m _ q)
... | inl q with preimage (j ∷_) (layouts (suc j) m k) q
...   | xs , r , refl = take (sound _ m _ r)
