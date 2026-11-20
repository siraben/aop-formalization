{-# OPTIONS --safe --without-K #-}
module AoP.LongestUpsequence where

open import AoP.Prelude
open import AoP.UpsequenceFrontier using (frontier)
open import AoP.UpsequenceDominance using (module Law)
open import AoP.UpsequenceSound using (sound)
open import AoP.UpsequenceCoverage using (cover)
open import AoP.Subsequences using (Subseq; _∈_; here; there)
open import AoP.ConversionCost using (len)
open import AoP.NatOrder using (_≤_; chain; rid; compare)
open import AoP.Polynomial using (inl; inr)
open import AoP.Relations using (nil; cons)
open import AoP.Refinement using (skip)
open import Agda.Builtin.Nat using (Nat)
open Law _≤_ using (Ordered) renaming (nil to ordered-empty)

-- Choose a longest survivor. The feasible empty subsequence ensures
-- even an empty candidate list has a safe initial incumbent.
module Choose (xs : List Nat) where
  Good : List Nat → Set
  Good ys = Subseq ys xs × Ordered ys
  empty-sub : ∀ (ts : List Nat) → Subseq [] ts
  empty-sub [] = nil refl
  empty-sub (a ∷ ts) = cons skip (empty-sub ts)

  scan : ∀ ts → (∀ {z} → z ∈ ts → Good z) → Σ (List Nat) λ w → Good w × (∀ {z} → z ∈ ts → len z ≤ len w)
  scan [] valid = [] , (empty-sub xs , ordered-empty) , λ ()
  scan (y ∷ ts) valid with scan ts (λ m → valid (there m))
  ... | w , ok , best with compare (len y) (len w)
  ...   | inl le = w , ok , λ { here → le ; (there m) → best m }
  ...   | inr ge = y , valid here , λ { here → rid _ ; (there m) → chain (best m) ge }

  solve : Σ (List Nat) λ w → Good w × (∀ z → Good z → len z ≤ len w)
  solve with scan (frontier xs) (sound xs)
  ... | w , ok , best = w , ok , λ z g → let v , mem , dom = cover (fst g) (snd g) in chain (fst dom) (best mem)

example : fst (Choose.solve (3 ∷ 1 ∷ 2 ∷ 2 ∷ [])) ≡ 1 ∷ 2 ∷ 2 ∷ []
example = refl
