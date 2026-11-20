{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourThinProjection where

open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Common.NatOrder using (_≤_; compare)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.25. Thin costed tours by comparing adjacent survivors.
-- Equal next-pairs compete on cost; different next-pairs both survive.
-- Erasing the costs gives exactly adjacent-run compaction of the keys,
-- independent of which cost wins (including ties).
module Law {Tour Key : Set} (key : Tour → Key) (cost : Tour → Nat)
           (eq : ∀ x y → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  bump : Tour → List Tour → List Tour
  bump t [] = t ∷ []
  bump t (u ∷ us) with eq (key t) (key u)
  ... | inr _ = t ∷ u ∷ us
  ... | inl _ with compare (cost t) (cost u)
  ...   | inl _ = t ∷ us
  ...   | inr _ = u ∷ us
  push : Key → List Key → List Key
  push k [] = k ∷ []
  push k (l ∷ ls) with eq k l
  ... | inl _ = l ∷ ls
  ... | inr _ = k ∷ l ∷ ls

  step : ∀ t us → map key (bump t us) ≡ push (key t) (map key us)
  step t [] = refl
  step t (u ∷ us) with eq (key t) (key u)
  ... | inr _ = refl
  ... | inl e with compare (cost t) (cost u)
  ...   | inl _ = cong (_∷ map key us) e
  ...   | inr _ = refl

  thin : List Tour → List Tour
  thin [] = []
  thin (t ∷ ts) = bump t (thin ts)
  compact : List Key → List Key
  compact [] = []
  compact (k ∷ ks) = push k (compact ks)
  projection : ∀ ts → map key (thin ts) ≡ compact (map key ts)
  projection [] = refl
  projection (t ∷ ts) = begin
    map key (bump t (thin ts)) ≡⟨ step t (thin ts) ⟩
    push (key t) (map key (thin ts)) ≡⟨ cong (push (key t)) (projection ts) ⟩
    compact (map key (t ∷ ts)) ∎
