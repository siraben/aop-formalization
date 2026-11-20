{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanGreedyDominance where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter08.Paragraph using (module Layout; _∷⁺_)
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Chapter07.VanGreedyStep using (module Law′)
open import AoP.Chapter07.SecurePartitionFold using () renaming (module Law to Guard)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Common.NatOrder using (rid)
open import AoP.Chapter02.Polynomial using (inr)
open import Agda.Builtin.Nat using (Nat)

-- Lift the four single-update comparisons to whole suffixes. The
-- greedy certificate records the failed extension whenever a new
-- block is opened. A competitor may open one even when extension fits.
module Proof (cap : Nat) where
  open Law Tx
  open Law′ cap
  open Guard cap using (Generated; base; fresh; extend)
  open Bank cap
  open Layout (λ (_ : Tx) → 0) 0 using (Para; new; glue)
  data Greedy : Tx → List Tx → Para → Set where
    start : ∀ w → Greedy w [] ((w ∷⁺ []) ∷⁺ [])
    split : ∀ {v vs p} w → (Secure (w ∷ first-block p) → ⊥) → Greedy v vs p → Greedy w (v ∷ vs) (new w p)
    join′ : ∀ {v vs p} w → Secure (w ∷ first-block p) → Greedy v vs p → Greedy w (v ∷ vs) (glue w p)

  dominates : ∀ {v vs p q} → Greedy v vs p → Generated v vs q → Better p q
  dominates (start w) (base .w _) = inr (rid 1 , keep w empty)
  dominates (split {p = p} w no g) (fresh {p = q} .w _ h) = new-vs-new w p q (dominates g h)
  dominates (split {p = p} w no g) (extend {l = u ∷⁺ us} {ls} .w ok h) = new-vs-glue w p ((u ∷⁺ us) ∷⁺ ls) (dominates g h) no ok
  dominates (join′ {p = p} w _ g) (fresh {p = q} .w _ h) = glue-new w p q (dominates g h)
  dominates (join′ {p = p} w _ g) (extend {l = u ∷⁺ us} {ls} .w _ h) = glue-glue w p ((u ∷⁺ us) ∷⁺ ls) (dominates g h)
