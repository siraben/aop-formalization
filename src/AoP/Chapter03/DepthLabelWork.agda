{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DepthLabelWork where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; map)
open import AoP.Chapter03.TipDepths using (depths)
open import AoP.Chapter03.DepthAccumulator using (label)
open import AoP.Chapter03.TipTraversalWork using (leaves; comb; comb-leaves)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
private variable A : Set

-- Exercise 3.48. Charge one successor for each tip label incremented by
-- a triangle map. At a fork both mapped subtrees contain exactly the
-- original tips; initial zero labels and tree constructors cost no
-- successors in this model. Each ancestor thus charges the tip once.
triangle-cost : Tree A → Nat
triangle-cost (tip _) = 0
triangle-cost (bin l r) = (triangle-cost l + triangle-cost r) + (leaves l + leaves r)

-- Instrument the reference program too. An increment pass returns its
-- rebuilt subtree and the number of successors applied at tips.
bump : Tree Nat → Tree Nat × Nat
bump (tip n) = tip (suc n) , 1
bump (bin l r) with bump l | bump r
... | lt , n | rt , m = bin lt rt , n + m
bump-exact : ∀ t → bump t ≡ (map suc t , leaves t)
bump-exact (tip n) = refl
bump-exact (bin l r) rewrite bump-exact l | bump-exact r = refl

private
  unchanged : ∀ s → leaves (map suc s) ≡ leaves s
  unchanged (tip _) = refl
  unchanged (bin a b) rewrite unchanged a | unchanged b = refl

shape : ∀ (t : Tree A) → leaves (depths t) ≡ leaves t
shape (tip _) = refl
shape (bin l r) rewrite unchanged (depths l) | unchanged (depths r) | shape l | shape r = refl

reference : Tree A → Tree Nat × Nat
reference (tip _) = tip 0 , 0
reference (bin l r) with reference l | reference r
... | lt , n | rt , m with bump lt | bump rt
...   | u , i | v , j = bin u v , (n + m) + (i + j)
reference-exact : ∀ (t : Tree A) → reference t ≡ (depths t , triangle-cost t)
reference-exact (tip _) = refl
reference-exact (bin l r) rewrite reference-exact l | reference-exact r
  | bump-exact (depths l) | bump-exact (depths r) | shape l | shape r = refl

-- The accumulator instead shares a single incremented depth between
-- the two recursive calls. Count this update at each fork, including
-- forks whose two tip labels happen to be equal.
forks : Tree A → Nat
forks (tip _) = 0
forks (bin l r) = suc (forks l + forks r)
run : Nat → Tree A → Tree Nat × Nat
run d (tip _) = tip d , 0
run d (bin l r) with suc d
... | next with run next l | run next r
...   | lt , n | rt , m = bin lt rt , suc (n + m)
exact : ∀ d (t : Tree A) → run d t ≡ (label d t , forks t)
exact d (tip _) = refl
exact d (bin l r) rewrite exact (suc d) l | exact (suc d) r = refl

private
  unit : ∀ n → n + 0 ≡ n
  unit 0 = refl
  unit (suc n) = cong suc (unit n)
-- On the comb with n forks, the accumulator makes n increments. Adding
-- a fork to this tree instead makes the triangle repeat one increment
-- on each of the enlarged tree's n+2 tips (cost 2+3+…+(n+1)).
linear : ∀ n → forks (comb n) ≡ n
linear 0 = refl
linear (suc n) rewrite linear n | unit n = refl
extra : ∀ n → triangle-cost (comb (suc n)) ≡ triangle-cost (comb n) + suc (suc n)
extra n rewrite unit (triangle-cost (comb n)) | comb-leaves n = cong (triangle-cost (comb n) +_) (cong suc (one n))
  where one : ∀ n → n + 1 ≡ suc n
        one 0 = refl
        one (suc n) = cong suc (one n)
