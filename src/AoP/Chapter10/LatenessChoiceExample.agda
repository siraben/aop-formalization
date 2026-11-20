{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.LatenessChoiceExample where

open import AoP.Common.Prelude
open import AoP.Chapter10.SignedLateness using (a; b; finite)
open import AoP.Chapter10.LatenessSchedule using (schedule)
open import AoP.Chapter10.LatenessOptimal using (peak)
import AoP.Chapter10.BackwardSchedule as Tardy
open import AoP.Chapter10.ScheduleSearch using (score)
open import Agda.Builtin.Int using (negsuc)

-- Jobs a and b both take one unit and have unit weight. Their due
-- dates are 4 and 8. At the common finish 2 both tardiness charges
-- vanish, so the original selector breaks the tie by placing a last.
-- Signed charges are -2 and -6: placing b last is strictly better.
input = a ∷ b ∷ []
signed-order : fst (schedule input) ≡ a ∷ b ∷ []
signed-order = refl
tardy-order : fst (Tardy.schedule input) ≡ b ∷ a ∷ []
tardy-order = refl
signed-peak : peak (fst (schedule input)) ≡ finite (negsuc 2)
signed-peak = refl
tardy-peak : peak (fst (Tardy.schedule input)) ≡ finite (negsuc 1)
tardy-peak = refl
same-tardiness : score (fst (schedule input)) ≡ score (fst (Tardy.schedule input))
same-tardiness = refl
