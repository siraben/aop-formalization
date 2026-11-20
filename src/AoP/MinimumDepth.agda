{-# OPTIONS --safe --without-K #-}
module AoP.MinimumDepth where

open import AoP.Prelude
open import AoP.Trees using (Tree; tip; bin)
open import Agda.Builtin.Nat using (Nat; zero; suc)
private variable A : Set

-- Exercise 3.49. Find the shallowest tip, counting edges from the root.
-- A tip in the left child gives an upper bound for the right child.
-- Carry the remaining distance to that bound: once it is zero, the
-- answer cannot improve, so return immediately without inspecting the tree.
min : Nat → Nat → Nat
min zero _ = zero
min (suc _) zero = zero
min (suc n) (suc m) = suc (min n m)

depth : Tree A → Nat
depth (tip _) = 0
depth (bin l r) = suc (min (depth l) (depth r))

limit : Nat → Tree A → Nat
limit zero _ = 0
limit (suc n) (tip _) = 0
limit (suc n) (bin l r) = suc (limit (limit n l) r)

private
  assoc : ∀ a b c → min (min a b) c ≡ min a (min b c)
  assoc zero b c = refl
  assoc (suc a) zero c = refl
  assoc (suc a) (suc b) zero = refl
  assoc (suc a) (suc b) (suc c) = cong suc (assoc a b c)

bounded : (t : Tree A) (n : Nat) → limit n t ≡ min n (depth t)
bounded t zero = refl
bounded (tip _) (suc n) = refl
bounded (bin l r) (suc n) = cong suc (begin
  limit (limit n l) r ≡⟨ bounded r (limit n l) ⟩
  min (limit n l) (depth r) ≡⟨ cong (λ b → min b (depth r)) (bounded l n) ⟩
  min (min n (depth l)) (depth r) ≡⟨ assoc n (depth l) (depth r) ⟩
  min n (min (depth l) (depth r)) ∎)

-- No initial bound: descend left until the first tip is found.
search : Tree A → Nat
search (tip _) = 0
search (bin l r) = suc (limit (search l) r)

correct : (t : Tree A) → search t ≡ depth t
correct (tip _) = refl
correct (bin l r) = cong suc (bounded r (search l) ∙ cong (λ b → min b (depth r)) (correct l))

-- A tip at depth one prunes the entire right subtree, even when its
-- shape is unknown (definitional equality, no induction on r).
prunes : (a : A) (r : Tree A) → search (bin (tip a) r) ≡ 1
prunes a r = refl
