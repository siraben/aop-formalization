{-# OPTIONS --safe --without-K #-}
module AoP.CylinderMoveExample where

open import AoP.Prelude
open import AoP.Cylinder using (module Grid)
open import AoP.FiveMoveCylinder using (up₂) renaming (module Grid to Five)
open import Agda.Builtin.Nat using (Nat)

-- Two columns on a five-row cylinder. Start at r0 at cost one.
-- The exit cell at r2 costs zero; all other exits cost nine. A single
-- adjacent step cannot reach r2, while a double upward step reaches it.
data Row : Set where r0 r1 r2 r3 r4 : Row
up down : Row → Row
up r0 = r1
up r1 = r2
up r2 = r3
up r3 = r4
up r4 = r0
down r0 = r4
down r1 = r0
down r2 = r1
down r3 = r2
down r4 = r3
first last : Row → Nat
first _ = 1
last r2 = 0
last _ = 9
module Three = Grid Row up down
module Wide = Five Row up down

three-price : Three.cost first r0 (fst (Three.solve first r0 (last ∷ []))) ≡ 10
three-price = refl
five-route : fst (Wide.solve first r0 (last ∷ [])) ≡ Wide.go up₂ Wide.exit
five-route = refl
five-price : Wide.cost first r0 (fst (Wide.solve first r0 (last ∷ []))) ≡ 1
five-price = refl
