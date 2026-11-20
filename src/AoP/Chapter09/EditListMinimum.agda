{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditListMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditScript
open import AoP.Chapter09.EditMinimum using (module Distance)
open import AoP.Chapter09.CachedEditCell using (module Cell)
open import AoP.Chapter09.CachedEditTable using (module Table)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (suc)

-- §9.2's external specification compares lists of commands whose
-- decoding gives the requested pair. Convert an arbitrary competing
-- list to a typed script, preserving one unit of cost per command.
module Solver {A : Set} (eq? : ∀ (x y : A) → Dec (x ≡ y)) where
  open Scripts {A}
  open Distance eq? using (cost)
  module C = Cell eq?
  open C.Entry using (best)
  open Table eq? using (solve)
  decode-cost : ∀ ops → cost (decode ops) ≡ len ops
  decode-cost [] = refl
  decode-cost (copy _ ∷ os) = cong suc (decode-cost os)
  decode-cost (delete _ ∷ os) = cong suc (decode-cost os)
  decode-cost (insert _ ∷ os) = cong suc (decode-cost os)
  erase-cost : ∀ {xs ys} (s : Script xs ys) → len (erase s) ≡ cost s
  erase-cost done = refl
  erase-cost (cpy s) = cong suc (erase-cost s)
  erase-cost (del s) = cong suc (erase-cost s)
  erase-cost (ins s) = cong suc (erase-cost s)

  commands : List A → List A → List (Op A)
  commands xs ys = erase (fst (best (solve xs ys)))
  endpoints : ∀ xs ys → edit (commands xs ys) ≡ (xs , ys)
  endpoints xs ys = feasible (fst (best (solve xs ys)))
  sym : ∀ {T : Set} {u v : T} → u ≡ v → v ≡ u
  sym refl = refl
  shortest : ∀ xs ys ops → edit ops ≡ (xs , ys) → len (commands xs ys) ≤ len ops
  shortest .(fst (edit ops)) .(snd (edit ops)) ops refl
    rewrite erase-cost (fst (best (solve (fst (edit ops)) (snd (edit ops)))) ) | sym (decode-cost ops) = snd (best (solve _ _)) (decode ops)
