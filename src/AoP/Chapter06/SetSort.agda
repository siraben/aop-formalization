{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SetSort where

open import AoP.Common.Prelude
open import AoP.Chapter06.Selection using (Lower; below; empty)
open import AoP.Chapter06.SelectionSort using (selection-sort; Sorted; nil; cons)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Chapter06.SelectionSort using (Perm; finish; emit)
open import AoP.Chapter06.Selection using (Remove; head; past)

-- Exercise 6.25. A list represents a finite set by membership. Sorting
-- alone allows [1,1] as an answer for {1}. Require each output key to
-- precede only *distinct* larger keys; now a repeated occurrence is
-- impossible. First selection-sort, then omit redundant occurrences.
record Same (xs ys : List Nat) : Set where
  constructor same
  field to : ∀ {a} → a ∈ xs → a ∈ ys
        from : ∀ {a} → a ∈ ys → a ∈ xs
open Same

data Strict : List Nat → Set where
  nil : Strict []
  cons : ∀ {a xs} → (∀ {b} → b ∈ xs → (a ≤ b) × (a ≡ b → ⊥)) → Strict xs → Strict (a ∷ xs)

member? : (a : Nat) (xs : List Nat) → (a ∈ xs) ⊎ (a ∈ xs → ⊥)
member? a [] = inr (λ ())
member? a (b ∷ xs) with eq a b
  where
  eq : (a b : Nat) → (a ≡ b) ⊎ (a ≡ b → ⊥)
  eq zero zero = inl refl
  eq zero (suc b) = inr (λ ())
  eq (suc a) zero = inr (λ ())
  eq (suc a) (suc b) with eq a b
  ... | inl refl = inl refl
  ... | inr no = inr λ { refl → no refl }
... | inl refl = inl here
... | inr neq with member? a xs
...   | inl m = inl (there m)
...   | inr no = inr λ { here → neq refl ; (there m) → no m }

lower : ∀ {a b xs} → Lower a xs → b ∈ xs → a ≤ b
lower (below le _) here = le
lower (below _ rest) (there m) = lower rest m

Result : List Nat → Set
Result xs = Σ _ λ ys → Same xs ys × Strict ys

compress : ∀ {xs} → Sorted xs → Result xs
compress nil = [] , same (λ ()) (λ ()) , nil
compress (cons {m = a} lb ok) with compress ok
... | ys , law , strict with member? a ys
...   | inl m = ys , same (λ { here → m ; (there k) → to law k }) (λ k → there (from law k)) , strict
...   | inr no = (a ∷ ys) , same (λ { here → here ; (there k) → there (to law k) })
                                  (λ { here → here ; (there k) → there (from law k) }) ,
                cons (λ k → lower lb (from law k) , λ { refl → no k }) strict

-- Read removal as an insertion to transport membership across selection.
import AoP.Chapter05.Permutations as P
open import AoP.Chapter06.PermutationGuard using (module Guard)
insert : ∀ {a xs ys} → Remove a ys xs → P.Insert a xs ys
insert head = P.front
insert (past p) = P.later (insert p)

backward-perm : ∀ {xs ys} → Perm xs ys → P.Perm ys xs
backward-perm finish = P.empty
backward-perm (emit rem p) = P.insert (backward-perm p) (insert rem)

sort : ∀ xs → Result xs
sort xs with selection-sort xs
... | ys , perm , ok with compress ok
...   | zs , law , strict = zs , same (λ k → to law (Guard.backward (backward-perm perm) k))
                                     (λ k → Guard.forward (backward-perm perm) (from law k)) , strict

example : fst (sort (2 ∷ 1 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ []
example = refl
