{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ChoiceProductFold where

open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.CartesianMenuPairs using (module Menus)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image; preimage)
open import AoP.Appendix.ListProduct using (Pick; none; one)
open import Agda.Builtin.Nat using (Nat)

-- §5.6. The list product chooses one entry per menu. Factor its update
-- into a Cartesian product (choose a head and a tail independently)
-- followed by map cons (build a single list from those choices).
module Derive {A : Set} where
  module M = Menus {A} {List A}
  cons : A × List A → List A
  cons (a , tail) = a ∷ tail
  step : List A → List (List A) → List (List A)
  step menu pool = map cons (M.cpp menu pool)
  run : List (List A) → List (List A)
  run [] = [] ∷ []
  run (menu ∷ menus) = step menu (run menus)

  -- Locate the pair used by map, then split its two membership
  -- witnesses. Repeating on the tail yields the specification Pick.
  sound : ∀ menus {xs} → xs ∈ run menus → Pick xs menus
  sound [] here = none
  sound [] (there ())
  sound (m ∷ ms) p with preimage cons (M.cpp m (run ms)) p
  ... | (a , tail) , edge , refl with fst (M.pairs m (run ms)) (a , tail) edge
  ...   | h , t = one h (sound ms t)
  complete : ∀ {menus xs} → Pick xs menus → xs ∈ run menus
  complete none = here
  complete (one {a} {m = m} {ms = ms} h t) = image cons (snd (M.pairs m (run ms)) (a , _) (h , complete t))

-- Two independent binary choices. The suffix pool is [[3],[4]];
-- prepending 1 and then 2 visits its two rows in that order.
example : Derive.run {Nat} ((1 ∷ 2 ∷ []) ∷ (3 ∷ 4 ∷ []) ∷ []) ≡
  (1 ∷ 3 ∷ []) ∷ (1 ∷ 4 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ (2 ∷ 4 ∷ []) ∷ []
example = refl
