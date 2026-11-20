{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CylinderExample where

open import AoP.Common.Prelude
open import AoP.Chapter07.Cylinder
open import AoP.Chapter07.CylinderEntry
open import Agda.Builtin.Nat using (Nat)

-- Reading the cylinder model (§7.4). With four rows, moving up from the
-- top enters the bottom row of the next column. Give the two ends of
-- this wraparound edge cost 1, and all other cells cost 9:
--
--            entry  exit
--   top        1      9
--   upper      9      9
--   lower      9      9
--   bottom     9      1
--
-- Only top → bottom can attain cost 2. This instance detects a boundary
-- error that an ordinary rectangular-grid model would miss.
data Row : Set where top upper lower bottom : Row

up down : Row → Row
up top = bottom
up upper = top
up lower = upper
up bottom = lower
down top = upper
down upper = lower
down lower = bottom
down bottom = top

entry-col exit-col : Row → Nat
entry-col top = 1
entry-col _ = 9
exit-col bottom = 1
exit-col _ = 9

open Grid Row up down
module S = Rim.Search Row up down entry-col (exit-col ∷ [])
rows = top ∷ upper ∷ lower ∷ bottom ∷ []
winner : S.Winner rows
winner = S.choose top (upper ∷ lower ∷ bottom ∷ [])

wraps : S.Winner.route winner ≡ rise exit
wraps = refl

starts-at-top : S.Winner.entry winner ≡ top
starts-at-top = refl

cost-two : cost entry-col (S.Winner.entry winner) (S.Winner.route winner) ≡ 2
cost-two = refl
