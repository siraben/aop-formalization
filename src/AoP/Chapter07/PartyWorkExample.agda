{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyWorkExample where

open import AoP.Common.Prelude
open import AoP.Chapter07.PartyExample using (Ada; rating; reports)
open import AoP.Chapter07.PartyPlanWork using (module Count)
open import AoP.Chapter07.PartyComparisons using () renaming (module Count to Comparisons)
open import AoP.Chapter01.Trees using (fork)
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import Agda.Builtin.Nat using (zero; _+_)

-- Ada supervises Bo and Cy. Count the three employee forks, the two
-- child links, and the three empty forests (one per employee). This
-- distinguishes the input-constructor unit from the comparison unit.
module Work = Count rating zero _+_ _≤_ rid chain sum-mono compare
module Cost = Comparisons rating zero _+_ _≤_ rid chain sum-mono compare
chart = fork Ada reports

comparisons : snd (Cost.tree chart) ≡ 3
comparisons = refl
construction : snd (Work.build chart) ≡ 8
construction = refl

-- The general two-pass theorem specializes to 16, including the
-- traversal that extracts names from the optimal plan.
open import AoP.Chapter07.PartyPlanTraversal using (module Law)
open import AoP.Chapter07.PartyCachedPlan using () renaming (module Law to Cached)
module Walk = Law rating zero _+_ _≤_ rid chain sum-mono compare
module Plans = Cached rating zero _+_ _≤_ rid chain sum-mono compare
both : snd (Work.build chart) + Walk.visits (Plans.Entry.plan (snd (fst (Work.build chart)))) ≡ 16
both = Work.two-pass chart
