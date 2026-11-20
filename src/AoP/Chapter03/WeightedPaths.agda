{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.WeightedPaths where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; map; foldt)
open import AoP.Chapter03.TipDepths using (tri)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Exercise 3.14. A tip contributes its label once per edge to the root.
-- Carry (weight, contribution): crossing an edge adds the first field
-- to the second. A tree triangle does this at every individual tip;
-- the fused program instead does it once per child at the fork.
Pair = Nat × Nat
lift : Pair → Pair
lift (w , c) = w , w + c
merge : Pair → Pair → Pair
merge (w , c) (v , d) = (w + v) , (c + d)
seed : Nat → Pair
seed w = w , 0

private
  assoc : ∀ x y z → (x + y) + z ≡ x + (y + z)
  assoc zero y z = refl
  assoc (suc x) y z = cong suc (assoc x y z)
  slide : ∀ x y → suc (x + y) ≡ x + suc y
  slide zero y = refl
  slide (suc x) y = cong suc (slide x y)
  swap : ∀ x y z → x + (y + z) ≡ y + (x + z)
  swap zero y z = refl
  swap (suc x) y z = cong suc (swap x y z) ∙ slide y (x + z)
  back : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
  back refl = refl

-- The Horner proviso: one extra edge before or after collecting the
-- two child summaries contributes exactly the same extra total weight.
distribute : ∀ p q → merge (lift p) (lift q) ≡ lift (merge p q)
distribute (w , c) (v , d) = cong ((w + v) ,_) (begin
  (w + c) + (v + d) ≡⟨ assoc w c (v + d) ⟩
  w + (c + (v + d)) ≡⟨ cong (w +_) (swap c v d) ⟩
  w + (v + (c + d)) ≡⟨ back (assoc w v (c + d)) ⟩
  (w + v) + (c + d) ∎)

collect = foldt (λ (x : Pair) → x) merge
promote : ∀ t → collect (map lift t) ≡ lift (collect t)
promote (tip x) = refl
promote (bin l r) rewrite promote l | promote r = distribute (collect l) (collect r)

reference : Tree Nat → Pair
reference t = collect (tri lift (map seed t))
scan : Tree Nat → Pair
scan = foldt seed (λ p q → lift (merge p q))

fusion : ∀ t → reference t ≡ scan t
fusion (tip _) = refl
fusion (bin l r) rewrite promote (tri lift (map seed l)) | promote (tri lift (map seed r))
                       | distribute (reference l) (reference r) | fusion l | fusion r = refl

-- Labels 2, 3, 5 occur at depths 1, 2, 2; their contributions sum to 18.
example : snd (scan (bin (tip 2) (bin (tip 3) (tip 5)))) ≡ 18
example = refl
