{-# OPTIONS --safe --without-K #-}
module AoP.PartitionLayerInverse where

open import AoP.Prelude
open import AoP.Paragraph using (_∷⁺_; module Layout)
open import AoP.Naturality using (_++_)
open import AoP.Relations using (Fold; nil; cons)

-- §5.6. For the fold with algebra [nil, new ∪ glue], a layer is
-- surjective because the first block is either a singleton or has
-- a second element. Nonempty blocks are essential to this split.
module Law (A : Set) where
  open Layout {Word = A} (λ _ → 0) 0 using (Line; flatten)
  Blocks = List Line
  data Step : Blocks → A × Blocks → Set where
    new : ∀ {x ps} → Step ((x ∷⁺ []) ∷ ps) (x , ps)
    glue : ∀ {x y ys ps} → Step ((x ∷⁺ (y ∷ ys)) ∷ ps) (x , (y ∷⁺ ys) ∷ ps)
  -- Both branches implement cons after concatenation. In the glue
  -- case the tail of the first block is appended before later blocks.
  commute : ∀ {p x ps} → Step p (x , ps) → flatten p ≡ x ∷ flatten ps
  commute new = refl
  commute glue = refl
  peel : ∀ l ps → Σ A λ x → Σ Blocks λ rest → Step (l ∷ ps) (x , rest)
  peel (x ∷⁺ []) ps = x , ps , new
  peel (x ∷⁺ (y ∷ ys)) ps = x , ((y ∷⁺ ys) ∷ ps) , glue

  Partition = Fold (_≡ []) Step
  sound : ∀ {p xs} → Partition p xs → flatten p ≡ xs
  sound (nil refl) = refl
  sound (cons {x} s h) = commute s ∙ cong (x ∷_) (sound h)
  -- Rebuild new/glue witnesses by consuming the original input;
  -- the commuting square recovers precisely the recursive equation.
  complete : ∀ xs p → flatten p ≡ xs → Partition p xs
  complete [] [] refl = nil refl
  complete [] ((x ∷⁺ ys) ∷ ps) ()
  complete (x ∷ xs) [] ()
  complete (x ∷ xs) (l ∷ ps) eq with peel l ps
  ... | y , rest , s with align (commute s) eq
    where
      align : ∀ {z a b ts us} → z ≡ a ∷ ts → z ≡ b ∷ us → (a ≡ b) × (ts ≡ us)
      align refl refl = refl , refl
  ...   | refl , tail-eq = cons s (complete xs rest tail-eq)
