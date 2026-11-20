{-# OPTIONS --safe --without-K #-}
module AoP.BracketFrontier where

open import AoP.Prelude
open import AoP.BracketSpineDecision using (module Check)
open import AoP.BracketSpine using (options; leaves; preserves)
open import AoP.BracketEnumeration using (placed)
open import AoP.ListProduct using (locate)
open import AoP.Thinning using (Thin)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Trees using (Tree; tip)
open import AoP.Naturality using (concat)
open import AoP.Horner using (map)
open import Agda.Builtin.Nat using (Nat)

-- For each nonempty suffix, extend only the trees retained for the
-- preceding stage, then thin before the next insertion. Every survivor
-- is a bracketing of the suffix; pruning never manufactures a tree.
module Build {A S : Set} (atom : A → S) (combine : S → S → S) (charge : S → S → Nat)
             (eq? : ∀ (x y : S) → Dec (x ≡ y)) where
  open Check.Thin atom combine charge eq? using (thinlist; correct)
  expand : A → List (Tree A) → List (Tree A)
  expand a ts = concat (map (options a) ts)
  pool : A → List A → List (Tree A)
  pool a [] = tip a ∷ []
  pool a (b ∷ xs) = thinlist (expand a (pool b xs))

  valid : ∀ a xs {t} → t ∈ pool a xs → leaves t ≡ a ∷ xs
  valid a [] here = refl
  valid a [] (there ())
  valid a (b ∷ xs) m with locate (options a) (pool b xs) (Thin.subset (correct (expand a (pool b xs))) m)
  ... | u , kept , pos = preserves (placed a u pos) ∙ cong (a ∷_) (valid b xs kept)
