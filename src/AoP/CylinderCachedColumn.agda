{-# OPTIONS --safe --without-K #-}
module AoP.CylinderCachedColumn where

open import AoP.Prelude
open import AoP.Cylinder using (module Grid)
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §7.4. One column update needs the *scores* of three suffixes.
-- Storing a witness path beside its score allows comparisons without
-- walking those paths again. Costs include both end columns.
module Table (Row : Set) (up down : Row → Row) where
  open Grid Row up down
  record Cell (c : Column) (r : Row) (cs : List Column) : Set where
    constructor cell
    field path : Path cs
          score : Nat
          exact : score ≡ cost c r path
          least : (p : Path cs) → score ≤ cost c r p
  open Cell
  end : ∀ c r → Cell c r []
  end c r = cell exit (c r) refl λ { exit → rid _ }

  data Move : Set where U S D : Move
  row : Move → Row → Row
  row U = up
  row S r = r
  row D = down
  extend : ∀ {d cs} → Move → Path cs → Path (d ∷ cs)
  extend U = rise
  extend S = stay
  extend D = fall
  charge : ∀ c r d {cs} m (p : Path cs) → c r + cost d (row m r) p ≡ cost c r (extend {d} m p)
  charge c r d U p = refl
  charge c r d S p = refl
  charge c r d D p = refl

  -- Compare up and straight, then compare the cheaper with down.
  pick : (f : Move → Nat) → Σ Move λ m → ∀ n → f m ≤ f n
  pick f with compare (f U) (f S)
  ... | inl us with compare (f U) (f D)
  ...   | inl ud = U , λ { U → rid _ ; S → us ; D → ud }
  ...   | inr du = D , λ { U → du ; S → chain du us ; D → rid _ }
  pick f | inr su with compare (f S) (f D)
  ... | inl sd = S , λ { U → su ; S → rid _ ; D → sd }
  ... | inr ds = D , λ { U → chain ds su ; S → ds ; D → rid _ }

  step : ∀ c r d {cs} → (∀ i → Cell d i cs) → Cell c r (d ∷ cs)
  step c r d {cs} next with pick (λ m → score (next (row m r)))
  ... | m , lowest = cell (extend m (path chosen)) (c r + score chosen)
      (cong (c r +_) (exact chosen) ∙ charge c r d m (path chosen))
      λ { (rise p) → bound U p ; (stay p) → bound S p ; (fall p) → bound D p }
    where chosen = next (row m r)
          bound : ∀ n (p : Path cs) → c r + score chosen ≤ c r + cost d (row n r) p
          bound n p = sum-mono (rid _) (chain (lowest n) (least (next (row n r)) p))
