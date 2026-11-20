{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.CachedEditCell where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditScript using (module Scripts)
open import AoP.Chapter09.EditMinimum using (module Distance)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.NatOrder using (_≤_; s≤; chain; compare)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- §9.2. Store each optimal script together with its length, so the
-- inner update compares stored numbers rather than traversing scripts.
module Cell {A : Set} (eq? : ∀ (x y : A) → Dec (x ≡ y)) where
  open Scripts {A}
  open Distance eq? using (cost; Best; cases; copy-best)
  record Entry (xs ys : List A) : Set where
    constructor entry
    field best : Best xs ys
          length : Nat
          exact : length ≡ cost (fst best)
  open Entry
  transport : ∀ {a b c d : Nat} → a ≡ c → b ≡ d → a ≤ b → c ≤ d
  transport refl refl p = p
  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()

  update : ∀ x y {xs ys} → Entry xs ys → Entry xs (y ∷ ys) → Entry (x ∷ xs) ys → Entry (x ∷ xs) (y ∷ ys)
  update x y diag down side with eq? x y
  ... | inl refl = entry (copy-best x (best diag)) (suc (length diag)) (cong suc (exact diag))
  ... | inr neq with compare (length down) (length side)
  ...   | inl le = entry ((del (fst (best down))) , cases (λ q e → absurd (neq e))
                (λ q → s≤ (snd (best down) q))
                (λ q → s≤ (chain (transport (exact down) (exact side) le) (snd (best side) q))))
                (suc (length down)) (cong suc (exact down))
  ...   | inr le = entry ((ins (fst (best side))) , cases (λ q e → absurd (neq e))
                (λ q → s≤ (chain (transport (exact side) (exact down) le) (snd (best down) q)))
                (λ q → s≤ (snd (best side) q)))
                (suc (length side)) (cong suc (exact side))
