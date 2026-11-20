{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineMergeOrder where

open import AoP.Common.Prelude
open import AoP.Chapter10.DeadlineMerge
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Common.NatOrder using (_≤_; chain)
open Job

-- A cons-oriented ordering certificate for merging: the first job
-- is due no later than any remaining job. Bounds on both input runs
-- transfer to every occurrence of the output, whichever side emits it.
Bound : Job → List Job → Set
Bound j xs = ∀ {k} → k ∈ xs → due j ≤ due k

data Sorted : List Job → Set where
  nil : Sorted []
  cons : ∀ {j js} → Bound j js → Sorted js → Sorted (j ∷ js)

bound : ∀ {j xs ys zs} → Trace xs ys zs → Bound j xs → Bound j ys → Bound j zs
bound (left-empty _) l r = r
bound (right-empty _) l r = l
bound (left _ m) l r here = l here
bound {j} (left _ m) l r (there p) = bound {j} m (λ q → l (there q)) r p
bound (right _ m) l r here = r here
bound {j} (right _ m) l r (there p) = bound {j} m l (λ q → r (there q)) p

extend : ∀ {x y ys} → due x ≤ due y → Bound y ys → Bound x (y ∷ ys)
extend xy rest here = xy
extend xy rest (there p) = chain xy (rest p)

ordered : ∀ {xs ys zs} → Trace xs ys zs → Sorted xs → Sorted ys → Sorted zs
ordered (left-empty _) _ r = r
ordered (right-empty _) l _ = l
ordered (left {x} {y = y} p m) (cons bx sx) ry@(cons by sy) = cons (bound {x} m bx (extend {x} {y} p by)) (ordered m sx ry)
ordered (right {x} {y = y} p m) lx@(cons bx sx) (cons by sy) = cons (bound {y} m (extend {y} {x} p bx) by) (ordered m lx sy)
