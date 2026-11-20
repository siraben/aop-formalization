{-# OPTIONS --safe --without-K #-}
module AoP.TourKeyTransition where

open import AoP.Prelude
open import AoP.TourKeyLayer using (module Keys)
open import AoP.TourThinProjection using (module Law)
open import AoP.TourRepeatedBlock using (module Block)
open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import AoP.Polynomial using (_⊎_)
open import AoP.Complement using (⊥)

-- Exercise 8.25. Collapse both middle runs in a *single* expansion.
-- No distinctness is needed here: compaction on the right also handles
-- coincidences with the neighbouring arms. The tails need not have the
-- same length; nonemptiness ensures a representative of each run.
module Layer (City : Set) where
  open Keys City
  module At (eq : ∀ (x y : Key) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
    open Law {Tour = Key} (λ k → k) (λ _ → 0) eq using (compact; push)
    open Block {City = City} eq using (reduce)
    private
      prefix : ∀ pre {xs ys} → compact xs ≡ compact ys → compact (pre ++ xs) ≡ compact (pre ++ ys)
      prefix [] p = p
      prefix (k ∷ ks) p = cong (push k) (prefix ks p)
      assoc : ∀ (xs ys zs : List Key) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
      assoc [] ys zs = refl
      assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)

    transition : ∀ b c u us v vs → let back = u ∷ us; front = v ∷ vs; old = L c back ++ R c front in
      compact (map (left b) old ++ map (right b) old) ≡
      compact (L b back ++ ((c , b) ∷ (b , c) ∷ R b front))
    transition b c u us v vs with streams b c (u ∷ us) (v ∷ vs)
    ... | e , f = let pre = L b (u ∷ us); post = R b (v ∷ vs)
                      l = repeat (c , b) (v ∷ vs); r = repeat (b , c) (u ∷ us)
                  in cong compact (cong (λ xs → xs ++ map (right b) (L c (u ∷ us) ++ R c (v ∷ vs))) e ∙ cong ((pre ++ l) ++_) f ∙ assoc pre l (r ++ post)) ∙
                     prefix pre {xs = l ++ (r ++ post)} {ys = (c , b) ∷ (b , c) ∷ post}
                       (reduce (c , b) vs (r ++ post) ∙ cong (push (c , b)) (reduce (b , c) us post))
