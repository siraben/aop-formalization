{-# OPTIONS --safe --without-K #-}
module AoP.KnapsackHead where

open import AoP.Prelude
open import AoP.KnapsackFrontier using (Summary; value)
open import AoP.KnapsackSortedBranches using (Desc)
open import AoP.KnapsackSortedTable using (module Table)
open import AoP.KnapsackTableCoverage using (module Search)
open import AoP.OrderedMeet using (module Order)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid; chain)
open import Agda.Builtin.Nat using (Nat)

-- §8.4. Replace a final maximum scan by taking the first entry. The
-- all-skip history ensures that even a zero-capacity table has a head.
module Solver (cap : Nat) where
  open Table cap
  open Search cap
  Answer : List Summary → Set
  Answer is = Σ Summary λ p → Run is p × (∀ {q} → Run is q → value q ≤ value p)

  private
    first : ∀ {p ps q} → Order.Ordered Desc (p ∷ ps) → q ∈ (p ∷ ps) → Desc p q
    first _ here = rid _
    first (Order.cons upper _) (there m) = upper m

    extract : ∀ is xs → Order.Ordered Desc xs → (∀ {p} → p ∈ xs → Run is p) →
              (∀ {q} → Run is q → Σ Summary λ p → (p ∈ xs) × (value q ≤ value p)) → Answer is
    extract is [] sorted legal cover′ with cover′ (all-skip is)
    ... | _ , () , _
    extract is (p ∷ ps) sorted legal cover′ = p , legal here , λ run →
      let rep = cover′ run in chain (snd (snd rep)) (first sorted (fst (snd rep)))

  solve : ∀ is → Answer is
  solve is = extract is (table is) (invariant is) (sound is) λ run →
    let rep = cover run in fst rep , fst (snd rep) , snd (snd (snd rep))

example : fst (Solver.solve 3 ((2 , 3) ∷ (3 , 5) ∷ (1 , 4) ∷ [])) ≡ (3 , 7)
example = refl
