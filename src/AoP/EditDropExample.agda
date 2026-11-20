{-# OPTIONS --safe --without-K #-}
module AoP.EditDropExample where

open import AoP.Prelude
open import AoP.EditScript
open import AoP.EditSuffix using (module Target)
open import AoP.EditDropCalculation using (module Calculation)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Follow the calculated inclusion, including its returned command list.
-- Removing the first target letter passes the leading deletion and
-- replaces the copy with a deletion. The final insertion survives.
open Scripts {Bool} using (edit)
open Target {Bool} using (drop)
open Calculation {Bool} using (inclusion)
script = delete true ∷ copy false ∷ insert true ∷ []
trimmed = fst (inclusion {a = script} (edit script , drop , refl))
commands : trimmed ≡ delete true ∷ delete false ∷ insert true ∷ []
commands = refl
endpoints : edit trimmed ≡ ((true ∷ false ∷ []) , (true ∷ []))
endpoints = refl

-- If the first target letter came from insertion, the same calculation
-- shortens the command list rather than replacing that command.
script′ = delete true ∷ insert false ∷ copy true ∷ []
shortens : fst (inclusion {a = script′} (edit script′ , drop , refl)) ≡ delete true ∷ copy true ∷ []
shortens = refl
