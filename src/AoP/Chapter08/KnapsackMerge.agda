{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackMerge where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier using (Summary; value)
open import AoP.Chapter08.KnapsackSortedBranches using (Desc; module Branch)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Common.NatOrder using (compare; chain)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)

-- §8.4. Merge the feasible take stream and the unchanged skip stream.
-- A trace records which stream supplied each occurrence, even on ties.
data Merge : List Summary → List Summary → List Summary → Set where
  nilL : ∀ ys → Merge [] ys ys
  nilR : ∀ xs → Merge xs [] xs
  left : ∀ {x y xs ys zs} → Desc x y → Merge xs (y ∷ ys) zs → Merge (x ∷ xs) (y ∷ ys) (x ∷ zs)
  right : ∀ {x y xs ys zs} → Desc y x → Merge (x ∷ xs) ys zs → Merge (x ∷ xs) (y ∷ ys) (y ∷ zs)

merge : ∀ xs ys → Σ _ (Merge xs ys)
merge [] ys = ys , nilL ys
merge (x ∷ xs) = walk
  where walk : ∀ ys → Σ _ (Merge (x ∷ xs) ys)
        walk [] = _ , nilR _
        walk (y ∷ ys) with compare (value y) (value x)
        ... | inl p with merge xs (y ∷ ys)
        ...   | zs , m = _ , left p m
        walk (y ∷ ys) | inr p with walk ys
        ...   | zs , m = _ , right p m

source : ∀ {xs ys zs p} → Merge xs ys zs → p ∈ zs → (p ∈ xs) ⊎ (p ∈ ys)
source (nilL _) p = inr p
source (nilR _) p = inl p
source (left _ m) here = inl here
source (right _ m) here = inr here
source (left _ m) (there p) with source m p
... | inl l = inl (there l)
... | inr r = inr r
source (right _ m) (there p) with source m p
... | inl l = inl l
... | inr r = inr (there r)

retain : ∀ {xs ys zs p} → Merge xs ys zs → (p ∈ xs) ⊎ (p ∈ ys) → p ∈ zs
retain (nilL _) (inr p) = p
retain (nilR _) (inl p) = p
retain (left _ m) (inl here) = here
retain (left _ m) (inl (there p)) = there (retain m (inl p))
retain (left _ m) (inr p) = there (retain m (inr p))
retain (right _ m) (inr here) = here
retain (right _ m) (inr (there p)) = there (retain m (inr p))
retain (right _ m) (inl p) = there (retain m (inl p))

ordered : ∀ {xs ys zs} → Merge xs ys zs → Order.Ordered Desc xs → Order.Ordered Desc ys → Order.Ordered Desc zs
ordered (nilL _) _ sy = sy
ordered (nilR _) sx _ = sx
ordered (left {x = x} {zs = zs} xy m) (Order.cons lx sx) sy@(Order.cons ly _) = Order.cons upper (ordered m sx sy)
  where upper : ∀ {p} → p ∈ zs → Desc x p
        upper p with source m p
        ... | inl l = lx l
        ... | inr here = xy
        ... | inr (there r) = chain (ly r) xy
ordered (right {y = y} {zs = zs} yx m) sx@(Order.cons lx _) (Order.cons ly sy) = Order.cons upper (ordered m sx sy)
  where upper : ∀ {p} → p ∈ zs → Desc y p
        upper p with source m p
        ... | inr r = ly r
        ... | inl here = yx
        ... | inl (there l) = chain (lx l) yx

-- A head comparison emits one cell. When either input ends, the
-- remaining stream is returned intact. Charge that suffix separately
-- to obtain an exact accounting even when one branch is empty.
open import Agda.Builtin.Nat using (Nat; suc; _+_)
private
  length : List Summary → Nat
  length [] = 0
  length (_ ∷ xs) = suc (length xs)
comparisons leftover : ∀ {xs ys zs} → Merge xs ys zs → Nat
comparisons (nilL _) = 0
comparisons (nilR _) = 0
comparisons (left _ m) = suc (comparisons m)
comparisons (right _ m) = suc (comparisons m)
leftover (nilL ys) = length ys
leftover (nilR xs) = length xs
leftover (left _ m) = leftover m
leftover (right _ m) = leftover m
account : ∀ {xs ys zs} (m : Merge xs ys zs) → comparisons m + leftover m ≡ length zs
account (nilL _) = refl
account (nilR _) = refl
account (left _ m) = cong suc (account m)
account (right _ m) = cong suc (account m)

sample : List Summary
sample = (3 , 5) ∷ (1 , 4) ∷ (0 , 0) ∷ []
worked : fst (merge (Branch.take 3 (2 , 3) sample) sample) ≡ (3 , 7) ∷ (3 , 5) ∷ (1 , 4) ∷ (2 , 3) ∷ (0 , 0) ∷ []
worked = refl
trace = snd (merge (Branch.take 3 (2 , 3) sample) sample)
worked-cost : (comparisons trace ≡ 4) × (leftover trace ≡ 1)
worked-cost = refl , refl
