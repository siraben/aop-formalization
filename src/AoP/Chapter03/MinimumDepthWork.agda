{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.MinimumDepthWork where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Chapter03.MinimumDepth using (limit; search; correct; depth)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
private variable A : Set

-- Exercise 3.49: count inspected tree constructors. When the remaining
-- distance is zero, the bound alone supplies the result; the tree can
-- stay unevaluated. The counter charges nothing for this call.
Answer = Nat × Nat
visit : Answer → Answer → Answer
visit (d , n) (e , m) = suc e , suc (n + m)
bounded : Nat → Tree A → Answer
bounded 0 t = 0 , 0
bounded (suc d) (tip _) = 0 , 1
bounded (suc d) (bin l r) with bounded d l
... | x , n = visit (x , n) (bounded x r)
run : Tree A → Answer
run (tip _) = 0 , 1
run (bin l r) with run l
... | x , n = visit (x , n) (bounded x r)

nodes : Tree A → Nat
nodes (tip _) = 1
nodes (bin l r) = suc (nodes l + nodes r)
-- Bound by structural induction on the tree, generalizing the remaining
-- distance. The right subtree's bound depends on the left result.
limited : ∀ (t : Tree A) d → (fst (bounded d t) ≡ limit d t) × (snd (bounded d t) ≤ nodes t)
limited t 0 = refl , z≤
limited (tip _) (suc d) = refl , s≤ z≤
limited (bin l r) (suc d) with bounded d l | limited l d
... | x , n | refl , le with bounded x r | limited r x
...   | y , m | refl , re = refl , s≤ (sum-mono le re)

certificate : ∀ (t : Tree A) → (fst (run t) ≡ search t) × (snd (run t) ≤ nodes t)
certificate (tip _) = refl , s≤ z≤
certificate (bin l r) with run l | certificate l
... | x , n | refl , le with bounded x r | limited r x
...   | y , m | refl , re = refl , s≤ (sum-mono le re)

minimum : ∀ (t : Tree A) → fst (run t) ≡ depth t
minimum t = fst (certificate t) ∙ correct t

-- An entire right subtree, however large, is skipped when the left
-- child is a tip. Only the root and that left tip were inspected.
skip : ∀ (a : A) r → run (bin (tip a) r) ≡ (1 , 2)
skip a r = refl

-- On any fork the bound is actually strict: descending through left
-- children eventually finds a fork with a tip at its left. At least
-- its right child escapes inspection. Propagate that saving up the tree.
nonempty : ∀ (t : Tree A) → 1 ≤ nodes t
nonempty (tip _) = s≤ z≤
nonempty (bin _ _) = s≤ z≤

saves-one : ∀ (l r : Tree A) → suc (snd (run (bin l r))) ≤ nodes (bin l r)
saves-one (tip _) r = s≤ (s≤ (nonempty r))
saves-one (bin a b) r = s≤ (sum-mono (saves-one a b) (snd (limited r (fst (run (bin a b))))))

-- Tightness: grow a left spine, always attaching a single right tip.
-- The first fork skips its right tip. Every higher fork gets a positive
-- left result and must inspect its right tip. Exactly one node is saved.
spine : Nat → Tree Nat
spine 0 = bin (tip 0) (tip 0)
spine (suc n) = bin (spine n) (tip 0)

tight : ∀ n → (fst (run (spine n)) ≡ 1) × (suc (snd (run (spine n))) ≡ nodes (spine n))
tight 0 = refl , refl
tight (suc n) with run (spine n) | tight n
... | .1 , count | refl , eq = refl , cong (λ x → suc (x + 1)) eq
