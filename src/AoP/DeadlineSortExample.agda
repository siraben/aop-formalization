{-# OPTIONS --safe --without-K #-}
module AoP.DeadlineSortExample where

open import AoP.Prelude
open import AoP.Tardiness using (Job; job)
open import AoP.ScheduleSearch using (score)
open import AoP.DeadlineSort using (sort; rounds; singles)
open import AoP.DeadlinePassCost using (work)

-- All weights are two. Processing the long, later-due job first
-- delays both earlier jobs. Sort by due date, keeping each duration.
late early middle : Job
late = job 4 6 2
early = job 2 1 2
middle = job 1 3 2
input = late ∷ early ∷ middle ∷ []
result : sort input ≡ early ∷ middle ∷ late ∷ []
result = refl
-- Completion times 4,6,7 yield penalties 0,10,8. In due-date order
-- the completion times are 2,3,7 and the penalties are 2,0,2.
original-peak : score input ≡ 10
original-peak = refl
sorted-peak : score (sort input) ≡ 2
sorted-peak = refl
-- Pass one compares late/early and carries middle. Pass two uses
-- two comparisons to merge [early,late] with [middle].
comparisons : work (rounds input) (singles input) ≡ 3
comparisons = refl
