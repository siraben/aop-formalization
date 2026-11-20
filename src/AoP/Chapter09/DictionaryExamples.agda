{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryExamples where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import Agda.Builtin.Maybe using (just)

-- §9.4. Read each pointer from its absolute offset in the growing
-- output. The second argument to ptr stores the copy length minus one.
data Letter : Set where a b c : Letter
open Text {Letter}

-- The third copied letter is read from the newly written part.
overlap-example : run (a ∷ b ∷ a ∷ []) (ptr 1 2 ∷ []) ≡ just (a ∷ b ∷ a ∷ b ∷ a ∷ b ∷ [])
overlap-example = refl

ten : run [] (sym a ∷ ptr 0 8 ∷ []) ≡ just (a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ a ∷ [])
ten = refl

mixed : run [] (sym a ∷ sym a ∷ sym b ∷ ptr 1 2 ∷ sym c ∷ ptr 1 1 ∷ []) ≡
        just (a ∷ a ∷ b ∷ a ∷ b ∷ a ∷ c ∷ a ∷ b ∷ [])
mixed = refl
