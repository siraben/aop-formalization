{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ConnectedSelectionSort where

open import AoP.Common.Prelude
open import AoP.Chapter06.PreorderSelection using (module Law)
open import AoP.Chapter05.Permutations using (Perm; Insert; empty; front; later; insert)
open import AoP.Chapter06.PermutationGuard using (module Guard)
open import AoP.Chapter06.QuickPermutation using (compose)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- §6.6. Repeatedly select a least key; tied but distinct values are
-- retained by the permutation witness. No test for key equality or
-- assumption of antisymmetry enters the recursion.
module Sort {A : Set} (R : A → A → Set) (tr : ∀ {x y z} → R x y → R y z → R x z)
            (cmp : ∀ x y → R x y ⊎ R y x) where
  open Law R tr cmp
  data Ordered : List A → Set where
    nil : Ordered []
    cons : ∀ {k ys} → Bound k ys → Ordered ys → Ordered (k ∷ ys)
  Answer : List A → Set
  Answer xs = Σ (List A) λ ys → Perm xs ys × Ordered ys

  private
    grows : ∀ {k : A} {xs ys} → Insert k xs ys → suc (len xs) ≡ len ys
    grows front = refl
    grows (later p) = cong suc (grows p)
    size : ∀ {xs ys : List A} → Perm xs ys → len xs ≡ len ys
    size empty = refl
    size (insert p i) = cong suc (size p) ∙ grows i
    budget : ∀ {i j n} → suc i ≡ suc j → i ≤ n → j ≤ n
    budget refl p = p

  run : ∀ n xs → len xs ≤ n → Answer xs
  run n [] p = [] , empty , nil
  run (suc n) (a ∷ xs) (s≤ le) with select a xs
  ... | chose k rs p bound with run n rs (budget (size p) le)
  ... | ys , perm , ord = (k ∷ ys) , compose p (insert perm front) , cons (λ mem → bound (Guard.backward perm mem)) ord

  sort : ∀ xs → Answer xs
  sort xs = run (len xs) xs (rid _)
