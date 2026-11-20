{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ReducedDictionaryTrace where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryTableTrace using (Letter; a; eq?; text)
open import AoP.Chapter09.ReducedDictionary using (module Reduced)
open import AoP.Chapter09.Compression using (module Text)
open Text {Letter}
module Run = Reduced eq? text 2 3

-- With a single previous a, a pointer would cost 3 and a literal 2.
-- At aaa the two-letter pointer costs 3 instead of two literals (4).
-- At aaaa the length-three pointer beats the pointer from the aa row.
two : fst (Run.fill [] ([] , refl) [] (a ∷ a ∷ [])) ≡ sym a ∷ sym a ∷ []
two = refl
three : fst (Run.fill [] ([] , refl) [] (a ∷ a ∷ a ∷ [])) ≡ sym a ∷ ptr 0 1 ∷ []
three = refl
four : fst Run.encode ≡ sym a ∷ ptr 0 2 ∷ []
four = refl
