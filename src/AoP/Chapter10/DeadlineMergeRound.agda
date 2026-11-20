{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineMergeRound where

open import AoP.Common.Prelude
open import AoP.Chapter10.DeadlineMerge using (merge; tests; linear)
open import AoP.Chapter10.DeadlineMergePermutation using (preserves)
open import AoP.Chapter10.DeadlineMergeOrder using (Sorted; ordered)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Permutations using (Perm)
open import AoP.Chapter05.PermuteTail using (identity)
open import AoP.Chapter06.QuickPermutation using (append-perm)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; sum-mono; z≤)
open import Agda.Builtin.Nat using (Nat; _+_)

-- A bottom-up merge round pairs consecutive runs. A lone last run
-- survives unchanged. Bound the number of comparisons in this whole
-- round by the number of jobs in its output, counting all runs.
Runs = List (List Job)
data Ordered : Runs → Set where
  nil : Ordered []
  cons : ∀ {xs rs} → Sorted xs → Ordered rs → Ordered (xs ∷ rs)
flat : Runs → List Job
flat [] = []
flat (r ∷ rs) = r ++ flat rs
mass : Runs → Nat
mass [] = 0
mass (r ∷ rs) = len r + mass rs
record Pass (rs : Runs) : Set where
  constructor pass
  field out : Runs
        comparisons : Nat
        cost-bound : comparisons ≤ mass out
        perm : Perm (flat rs) (flat out)
        sorted : Ordered rs → Ordered out

private
  assoc : ∀ (xs ys zs : List Job) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)
  back : ∀ {a b : List Job} → a ≡ b → b ≡ a
  back refl = refl
  group : ∀ x y rs {z zs} → Perm (x ++ y) z → Perm (flat rs) (flat zs) → Perm (flat (x ∷ y ∷ rs)) (flat (z ∷ zs))
  group x y rs {z} {zs} p q rewrite back (assoc x y (flat rs)) = append-perm p q

round : ∀ rs → Pass rs
round [] = pass [] 0 z≤ (identity []) (λ p → p)
round (r ∷ []) = pass (r ∷ []) 0 z≤ (identity _) (λ p → p)
round (x ∷ y ∷ rs) with merge x y | round rs
... | z , m | pass zs n le p ord = pass (z ∷ zs) (tests m + n) (sum-mono (linear m) le)
    (group x y rs {z} {zs} (preserves m) p) λ { (cons sx (cons sy rest)) → cons (ordered m sx sy) (ord rest) }
