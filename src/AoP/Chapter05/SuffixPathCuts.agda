{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SuffixPathCuts where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter06.TreeMemberPath using (Path; stop; via)
open import AoP.Chapter06.ListMemberPath using (Tail; drop)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter05.ZippedSplits using (tails)

-- §5.6. Each tail step discards precisely one leading cell. Reading
-- the discarded heads in step order recovers the prefix before the
-- cut. In the enumeration the same step skips one candidate suffix.
module Law {A : Set} where
  cut : ∀ {p xs : List A} → Path Tail p xs → Σ _ (λ front → front ++ p ≡ xs)
  cut stop = [] , refl
  cut (via (drop {x = x}) path) with cut path
  ... | front , eq = (x ∷ front) , cong (x ∷_) eq
  remove : ∀ (front p : List A) → Path Tail p (front ++ p)
  remove [] p = stop
  remove (x ∷ front) p = via drop (remove front p)

  whole : ∀ (xs : List A) → xs ∈ tails xs
  whole [] = here
  whole (x ∷ xs) = here
  enumerate : ∀ {p xs : List A} → Path Tail p xs → p ∈ tails xs
  enumerate {xs = xs} stop = whole xs
  enumerate (via drop path) = there (enumerate path)
  justify : ∀ (xs : List A) {p} → p ∈ tails xs → Path Tail p xs
  justify [] here = stop
  justify [] (there ())
  justify (x ∷ xs) here = stop
  justify (x ∷ xs) (there found) = via drop (justify xs found)
