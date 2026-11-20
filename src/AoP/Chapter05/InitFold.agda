{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.InitFold where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Chapter01.NonemptyFolds using (fold⁺)
open import AoP.Chapter01.Naturality using (_++_)
private variable A : Set

-- Exercise 5.24. Drop the final element of a nonempty list. The
-- singleton contributes nothing; each earlier cons is retained. Show
-- that adjoining the discarded element reconstructs the input and
-- that every snoc decomposition yields this same prefix.
init : Nonempty A → List A
init = fold⁺ (λ _ → []) _∷_

witness : (a : A) (xs : List A) → Σ A λ z → init (a ∷⁺ xs) ++ (z ∷ []) ≡ a ∷ xs
witness a [] = a , refl
witness a (b ∷ bs) with witness b bs
... | z , eq = z , cong (a ∷_) eq

unique : (prefix : List A) (z a : A) (xs : List A) → prefix ++ (z ∷ []) ≡ a ∷ xs → prefix ≡ init (a ∷⁺ xs)
unique [] z .z .[] refl = refl
unique (b ∷ []) z a [] ()
unique (b ∷ c ∷ bs) z a [] ()
unique (b ∷ bs) z a (c ∷ cs) eq = cong (_∷ bs) (head-eq eq) ∙ cong (a ∷_) (unique bs z c cs (tail-eq eq))
  where
  head-eq : ∀ {x y : A} {us vs} → x ∷ us ≡ y ∷ vs → x ≡ y
  head-eq refl = refl
  tail-eq : ∀ {x y : A} {us vs} → x ∷ us ≡ y ∷ vs → us ≡ vs
  tail-eq refl = refl
