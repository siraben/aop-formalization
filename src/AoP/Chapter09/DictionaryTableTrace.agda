{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryTableTrace where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter02.Polynomial using (inl)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter09.UniformCodeCost using (module Law)

data Letter : Set where a : Letter
eq? : (x y : Letter) → Dec (x ≡ y)
eq? a a = inl refl
open Text {Letter}
text = a ∷ a ∷ a ∷ a ∷ []
-- Literal charge 2, pointer charge 3: a one-letter copy cannot
-- improve two literals, while an overlapping three-letter copy wins.
module Run = Table eq? text 2 3
one : fst (Run.fill [] ([] , refl) [] (a ∷ [])) ≡ sym a ∷ []
one = refl
two : fst (Run.fill [] ([] , refl) [] (a ∷ a ∷ [])) ≡ sym a ∷ sym a ∷ []
two = refl
four : fst Run.encode ≡ sym a ∷ ptr 0 2 ∷ []
four = refl
cost : Law.bits 2 3 (fst Run.encode) ≡ 5
cost = refl
