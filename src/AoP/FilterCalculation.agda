{-# OPTIONS --safe --without-K #-}
module AoP.FilterCalculation where

open import AoP.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import AoP.Horner using (map)
open import AoP.Inverses using (zip)
open import AoP.PointFree using (wrapIf; filter; zip-map)
open import AoP.Functors using (map-comp; map-resp)
open import AoP.Naturality using (concat; concat-natural)

-- §1.7. Slide the projection through concatenation, then fuse adjacent
-- maps. Only the pointwise rule for the Boolean guard needs cases.
module Derivation {A : Set} (p : A → Bool) where
  Pair = A × Bool
  tag : A → Pair
  tag x = x , p x
  keep : Pair → List Pair
  keep z = wrapIf (snd z) z
  pick : Pair → List A
  pick z = wrapIf (snd z) (fst z)
  distribute : ∀ z → map fst (keep z) ≡ pick z
  distribute (x , true) = refl
  distribute (x , false) = refl

  back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  back refl = refl

  calculate : ∀ xs → map fst (filter snd (zip xs (map p xs))) ≡ filter p xs
  calculate xs = let zs = zip xs (map p xs) in begin
    map fst (concat (map keep zs))
      ≡⟨ concat-natural fst (map keep zs) ⟩
    concat (map (map fst) (map keep zs))
      ≡⟨ cong concat (back (map-comp (map fst) keep zs)) ⟩
    concat (map (λ z → map fst (keep z)) zs)
      ≡⟨ cong concat (map-resp distribute zs) ⟩
    concat (map pick zs)
      ≡⟨ cong (λ tags → concat (map pick tags)) (zip-map p xs) ⟩
    concat (map pick (map tag xs))
      ≡⟨ cong concat (back (map-comp pick tag xs)) ⟩
    concat (map (λ x → pick (tag x)) xs)
      ≡⟨⟩
    filter p xs ∎
