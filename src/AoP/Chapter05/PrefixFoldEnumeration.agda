{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PrefixFoldEnumeration where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image; preimage)
open import AoP.Chapter05.PrefixFoldCuts using (module Law)
open import AoP.Chapter05.ZippedSplits using (inits)

-- §5.6. The stop branch emits [] once, regardless of how many tail
-- answers it could ignore. This is legitimate because the tail always
-- has at least one prefix (namely []). The retain branch maps cons
-- over all tail answers. Membership, rather than proof multiplicity,
-- is what the implementation must preserve.
module With {A : Set} where
  open Law {A}
  open import AoP.Chapter04.Relations using (nil; cons)
  enumerate : ∀ {xs p} → Prefix p xs → p ∈ inits xs
  enumerate (nil refl) = here
  enumerate (cons halt h) = here
  enumerate (cons {x} retain h) = there (image (x ∷_) (enumerate h))
  justify : ∀ xs {p} → p ∈ inits xs → Prefix p xs
  justify [] here = nil refl
  justify [] (there ())
  justify (a ∷ xs) here = cons halt (empty xs)
  justify (a ∷ xs) (there m) with preimage (a ∷_) (inits xs) m
  ... | p , h , refl = cons retain (justify xs h)
