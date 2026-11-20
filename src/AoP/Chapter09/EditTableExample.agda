{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditTableExample where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditListMinimum using (module Solver)
open import AoP.Chapter09.EditScript using (copy; insert; delete)
open import AoP.Chapter09.CachedEditCell using (module Cell)
open import AoP.Chapter09.CachedEditTable using (module Table)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

data Letter : Set where a b : Letter
equal? : ∀ (x y : Letter) → Dec (x ≡ y)
equal? a a = inl refl
equal? a b = inr (λ ())
equal? b a = inr (λ ())
equal? b b = inl refl
module T = Table equal?
module C = Cell equal?

-- Edit ab to ba. Show the cached costs for all nine suffix pairs.
-- Columns correspond to ba, a, and the empty target, in that order.
row-costs : ∀ {xs ys} → T.Row xs ys → List Nat
row-costs (T.end e) = C.Entry.length e ∷ []
row-costs (T.next e r) = C.Entry.length e ∷ row-costs r
source = a ∷ b ∷ []
target = b ∷ a ∷ []
bottom : row-costs (T.rows [] target) ≡ 2 ∷ 1 ∷ 0 ∷ []
bottom = refl
middle : row-costs (T.rows (b ∷ []) target) ≡ 2 ∷ 2 ∷ 1 ∷ []
middle = refl
top : row-costs (T.rows source target) ≡ 3 ∷ 2 ∷ 2 ∷ []
top = refl
-- Delete and insert tie at the first cell. The implemented comparison
-- chooses deletion, then copies the matching b and inserts the last a.
script : Solver.commands equal? source target ≡ delete a ∷ copy b ∷ insert a ∷ []
script = refl
