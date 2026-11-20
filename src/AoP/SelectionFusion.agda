{-# OPTIONS --safe --without-K #-}
module AoP.SelectionFusion where

open import AoP.Prelude
open import AoP.Selection using (Remove; head; past; Lower; below; Choice; select)
open import AoP.SelectionSort using (remove-bound)
open import AoP.Permutations using (Perm; Insert; insert; front; later)
open import AoP.PermutationGuard using (module Guard)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)

-- §6.6, selection fusion proviso. Read the reversible removal as
-- insertion. If a candidate suffix permutes to the selected remainder,
-- then consing the minimum permutes to the whole original input; the
-- minimum guard transfers backwards along that same suffix permutation.
undo : ∀ {a xs rs} → Remove a xs rs → Insert a rs xs
undo head = front
undo (past r) = later (undo r)

at : ∀ {a b xs} → Lower a xs → b ∈ xs → a ≤ b
at (below le _) here = le
at (below _ rest) (there m) = at rest m

proviso : ∀ {xs ys} (c : Choice xs) → Perm ys (Choice.rest c) →
          Perm (Choice.minimum c ∷ ys) xs × (∀ {b} → b ∈ ys → Choice.minimum c ≤ b)
proviso c p = insert p (undo (Choice.removal c)) , λ m →
  at (snd (remove-bound (Choice.removal c) (Choice.bound c))) (Guard.forward p m)

selected : ∀ x xs {ys} → let c = select x xs in Perm ys (Choice.rest c) →
           Perm (Choice.minimum c ∷ ys) (x ∷ xs) × (∀ {b} → b ∈ ys → Choice.minimum c ≤ b)
selected x xs = proviso (select x xs)
