{-# OPTIONS --safe --without-K #-}
module AoP.InverseDomains where

open import AoP.Prelude
open import AoP.Inverses
open import AoP.Horner using (map)
open import AoP.Complement using (⊥)
open import AoP.DecimalPoint using (whole)
open import AoP.DecimalDigits using (oh; Digit)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import Agda.Builtin.Nat using (Nat)
private variable A B : Set

-- §1.5. The two projections over a list of pairs can share one fold.
projections : (ps : List (A × B)) → unzip ps ≡ (map fst ps , map snd ps)
projections [] = refl
projections ((a , b) ∷ ps) rewrite projections ps = refl

-- Equal lengths characterize exactly the image of unzip. The reverse
-- direction uses zip to construct a preimage, not just a length test.
aligned : (ps : List (A × B)) → Aligned (fst (unzip ps)) (snd (unzip ps))
aligned [] = empty
aligned ((a , b) ∷ ps) = next (aligned ps)

image : ∀ {xs : List A} {ys : List B} → Aligned xs ys → Σ _ λ ps → unzip ps ≡ (xs , ys)
image {xs = xs} {ys} ok = zip xs ys , unzip-zip ok

-- A different obstruction occurs for decimal digits with leading zeros:
-- the empty sequence and a single zero evaluate alike. A left inverse
-- would have to recover both sequences from zero.
no-left-inverse : (print : Nat → Snoc Digit) → (∀ ds → print (whole ds) ≡ ds) → ⊥
no-left-inverse print law with back (law ε) ∙ law (ε ▻ oh)
  where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
        back refl = refl
... | ()
