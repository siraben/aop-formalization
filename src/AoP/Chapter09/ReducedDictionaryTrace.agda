{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ReducedDictionaryTrace where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryTableTrace using (Letter; a; eq?; text)
open import AoP.Chapter09.ReducedDictionary using (module Reduced)
open import AoP.Chapter09.DictionaryCachedRows using (module Rows)
open import AoP.Chapter09.DictionarySplice using (module Splice)
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

-- Read the same result through the cached encoder. The first step
-- uses the simulation theorem rather than reducing a second search.
module Cached = Rows eq? text 2 3
cached-program : fst (fst Cached.encode) ≡ sym a ∷ ptr 0 2 ∷ []
cached-program = begin
  fst (fst Cached.encode) ≡⟨ cong fst Cached.agrees ⟩
  fst Run.encode          ≡⟨ four ⟩
  sym a ∷ ptr 0 2 ∷ []    ∎

cached-price : Cached.Cost.value (snd Cached.encode) ≡ 5
cached-price = begin
  Cached.Cost.value (snd Cached.encode)        ≡⟨ Cached.optimum-price ⟩
  price (fst Run.encode)                       ≡⟨ cong price four ⟩
  price (sym a ∷ ptr 0 2 ∷ [])                 ≡⟨⟩
  5 ∎
  where open Splice {Letter} 2 3 using (price)
