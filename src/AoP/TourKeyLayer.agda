{-# OPTIONS --safe --without-K #-}
module AoP.TourKeyLayer where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_; map-++)

-- Exercise 8.25. Keys before extending the tour with first city b
-- have two arms: (u,c) in reverse input order, then (c,u) in forward
-- order. Each map preserves one arm and makes the other arm constant.
module Keys (City : Set) where
  Key = City × City
  left right : City → Key → Key
  left b p = fst p , b
  right b p = b , snd p
  L R : City → List City → List Key
  L c = map (λ u → u , c)
  R c = map (λ u → c , u)
  repeat : Key → List City → List Key
  repeat p = map (λ _ → p)

  ll : ∀ b c us → map (left b) (L c us) ≡ L b us
  ll b c [] = refl
  ll b c (u ∷ us) = cong ((u , b) ∷_) (ll b c us)
  lr : ∀ b c us → map (left b) (R c us) ≡ repeat (c , b) us
  lr b c [] = refl
  lr b c (u ∷ us) = cong ((c , b) ∷_) (lr b c us)
  rl : ∀ b c us → map (right b) (L c us) ≡ repeat (b , c) us
  rl b c [] = refl
  rl b c (u ∷ us) = cong ((b , c) ∷_) (rl b c us)
  rr : ∀ b c us → map (right b) (R c us) ≡ R b us
  rr b c [] = refl
  rr b c (u ∷ us) = cong ((b , u) ∷_) (rr b c us)

  streams : ∀ b c back front → let old = L c back ++ R c front in
    (map (left b) old ≡ L b back ++ repeat (c , b) front) ×
    (map (right b) old ≡ repeat (b , c) back ++ R b front)
  streams b c back front rewrite map-++ (left b) (L c back) (R c front) | map-++ (right b) (L c back) (R c front) | ll b c back | lr b c front | rl b c back | rr b c front = refl , refl
