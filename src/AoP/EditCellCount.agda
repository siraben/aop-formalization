{-# OPTIONS --safe --without-K #-}
module AoP.EditCellCount where

open import AoP.Prelude
open import AoP.EditMinimum using (module Distance)
open import AoP.ConversionCost using (len)
open import AoP.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- §9.2. Count interior cell updates, excluding the initialized bottom
-- row and end column. Each more constructor visited by advance triggers
-- one Update.cell; last triggers none. The actual input strip of each
-- advance is tabulate xs ys, as in the tabulation recurrence.
module Count {A : Set} (equal? : ∀ (x y : A) → Dec (x ≡ y)) where
  open Distance equal?
  visits : ∀ {xs ys} → Strip xs ys → Nat
  visits (last _) = 0
  visits (more _ s) = suc (visits s)
  width : ∀ {xs ys} (s : Strip xs ys) → visits s ≡ len ys
  width (last _) = refl
  width (more _ s) = cong suc (width s)

  cells : List A → List A → Nat
  cells [] ys = 0
  cells (x ∷ xs) ys = visits (tabulate xs ys) + cells xs ys
  exact : ∀ xs ys → cells xs ys ≡ len xs * len ys
  exact [] ys = refl
  exact (x ∷ xs) ys = begin
    visits (tabulate xs ys) + cells xs ys ≡⟨ cong (_+ cells xs ys) (width (tabulate xs ys)) ⟩
    len ys + cells xs ys ≡⟨ cong (len ys +_) (exact xs ys) ⟩
    len (x ∷ xs) * len ys ∎
