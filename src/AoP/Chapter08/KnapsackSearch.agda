{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackSearch where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier
open import AoP.Chapter08.Thinning using (Thin; thin-compose; thin-id)
open import AoP.Chapter05.Subsequences using (_∈_; merge; split; image; preimage)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (rid; chain)

-- §8.4. For every item, either add its weight and value or skip it.
-- Exhaustive search keeps both branches for every partial packing.
-- Instead we prune after *each* item: is a summary discarded early
-- still dispensable after several more items? The invariant below
-- compares the reduced table with the whole exhaustive search.
branch : Summary → List Summary → List Summary
branch i ps = map (i ⊞_) ps ++ ps

all table : List Summary → List Summary
all [] = (0 , 0) ∷ []
all (i ∷ is) = branch i (all is)
table [] = (0 , 0) ∷ []
table (i ∷ is) = Sweep.thinlist (branch i (table is))

Covers : List Summary → List Summary → Set
Covers ps qs = Thin _≼_ (_∈ ps) (_∈ qs)

branches : ∀ i ps qs → Covers ps qs → Covers (branch i ps) (branch i qs)
Thin.subset (branches i ps qs t) p with split (map (i ⊞_) ps) ps p
... | inr y = merge (map (i ⊞_) qs) qs (inr (Thin.subset t y))
... | inl y with preimage (i ⊞_) ps y
...   | x , z , refl = merge (map (i ⊞_) qs) qs (inl (image (i ⊞_) (Thin.subset t z)))
Thin.cover (branches i ps qs t) q p with split (map (i ⊞_) qs) qs p
... | inr y with Thin.cover t q y
...   | r , z , le = r , merge (map (i ⊞_) ps) ps (inr z) , le
Thin.cover (branches i ps qs t) q p | inl y with preimage (i ⊞_) qs y
... | x , z , refl with Thin.cover t x z
...   | r , w , le = (i ⊞ r) , merge (map (i ⊞_) ps) ps (inl (image (i ⊞_) w)) , extend i le

invariant : ∀ is → Covers (table is) (all is)
invariant [] = thin-id (λ _ → rid _ , rid _)
invariant (i ∷ is) = thin-compose (λ p q → chain (fst p) (fst q) , chain (snd q) (snd p))
  (Sweep.correct (branch i (table is))) (branches i (table is) (all is) (invariant is))

optimal : ∀ cap is p → Maximum (Feasible cap (_∈ table is)) p → Maximum (Feasible cap (_∈ all is)) p
optimal cap is = preserve cap _ _ (invariant is)
