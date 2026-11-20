{-# OPTIONS --safe --without-K #-}
module AoP.SurjectiveFoldEquality where

open import AoP.Categories
open import AoP.ProductAllegory using (Laws)

-- §6.5, final comparison in Theorem 6.4. Here h is the fold and f
-- assigns each output its tree. Fusion supplies f ∘ h ⊑ id, and the
-- preceding accessibility argument establishes surjectivity of h.
module Proof {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  private
    rid : ∀ {A B} {x : Hom A B} → x ⊑ x
    rid = respect reflexive
  module At {A I} (f : Hom A I) (h : Hom I A)
    (entire : identity ⊑ (rev f ∘ f)) (onto : identity ⊑ (h ∘ rev h))
    (sound : (f ∘ h) ⊑ identity) where
    forward : h ⊑ rev f
    forward = trans (respect (symmetric (unitˡ h))) (trans (mono entire rid)
      (trans (respect (assoc _ _ _)) (trans (mono rid sound) (respect (unitʳ _)))))
    -- Insert a preimage for the output, then reverse the soundness
    -- inequality to contract h˘ ∘ f˘. Only the two indicated units
    -- are needed; no choice of a global section is involved.
    backward : rev f ⊑ h
    backward = trans (respect (symmetric (unitˡ _))) (trans (mono onto rid)
      (trans (respect (assoc _ _ _)) (trans (mono rid small) (respect (unitʳ _)))))
      where
        open import AoP.AllegoryMapComposition using (module Law)
        small = trans (respect (symmetric (flip f h))) (trans (rev-mono sound) (respect (Law.reverse-id L)))
    equality : h ≈ rev f
    equality = antisym forward backward
