{-# OPTIONS --safe --without-K #-}
module AoP.CachedEditTable where

open import AoP.Prelude
open import AoP.CachedEditCell using (module Cell)
open import AoP.EditScript using (module Scripts)
open import AoP.NatOrder using (rid; s≤)
open import AoP.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (suc)

-- §9.2. Each row contains a cached optimum for every target suffix.
-- Advancing the row uses the old diagonal and below entries and the
-- already computed entry to the right. Both boundaries increment a
-- known length when introducing their only possible command.
module Table {A : Set} (eq? : ∀ (x y : A) → Dec (x ≡ y)) where
  open Cell eq?
  open Scripts {A}
  data Row (xs : List A) : List A → Set where
    end : Entry xs [] → Row xs []
    next : ∀ {y ys} → Entry xs (y ∷ ys) → Row xs ys → Row xs (y ∷ ys)
  top : ∀ {xs ys} → Row xs ys → Entry xs ys
  top (end e) = e
  top (next e _) = e
  base : ∀ ys → Row [] ys
  base [] = end (entry (done , λ { done → rid 0 }) 0 refl)
  base (y ∷ ys) with base ys
  ... | r with top r
  ...   | entry (s , opt) n eq = next (entry (ins s , λ { (ins q) → s≤ (opt q) }) (suc n) (cong suc eq)) r
  advance : ∀ x {xs ys} → Row xs ys → Row (x ∷ xs) ys
  advance x (end (entry (s , opt) n eq)) = end (entry (del s , λ { (del q) → s≤ (opt q) }) (suc n) (cong suc eq))
  advance x (next {y} below tail) with advance x tail
  ... | r = next (update x y (top tail) below (top r)) r
  rows : ∀ xs ys → Row xs ys
  rows [] ys = base ys
  rows (x ∷ xs) ys = advance x (rows xs ys)
  solve : ∀ xs ys → Entry xs ys
  solve xs ys = top (rows xs ys)
