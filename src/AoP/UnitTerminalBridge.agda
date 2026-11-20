{-# OPTIONS --safe --without-K #-}
module AoP.UnitTerminalBridge where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.RelUnitObject using (UnitObject; module Extract; module Build)
open import AoP.UniversalObjects using (module Universal)
open import AoP.Tabulation using (module Table)

-- §4.3 in concrete Rel. From an allegory unit there is just one way
-- to end a function: take its unique point. For the converse, tabulate
-- an arbitrary scalar R on the proposed terminal object. Both columns
-- go from the same row type to U and must therefore agree. Every edge
-- has a row, so both of its endpoints agree, as the scalar law asks.
module U = Universal Fun
terminal : ∀ {X} → UnitObject X → U.Terminal X
U.Terminal.enter (terminal unit) A a = Extract.point unit
U.Terminal.unique (terminal unit) f a = Extract.same unit _ _

unit : ∀ {X} → U.Terminal X → UnitObject X
UnitObject.scalar (unit t) R {b} {a} edge = left ∙ back right
  where open Table R
        r = row b a edge
        left = U.Terminal.unique t target r
        right = U.Terminal.unique t source r
        back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
        back refl = refl
UnitObject.cover (unit t) A = (λ x a → U.Terminal.enter t A a ≡ x) , (λ { refl → _ , refl , refl })
