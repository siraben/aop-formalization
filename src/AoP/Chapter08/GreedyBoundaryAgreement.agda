{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.GreedyBoundaryAgreement where

open import AoP.Common.Prelude
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter07.LongestPrefix using (module Prefix)
open import AoP.Chapter08.LongestPrefixUnique using (module Unique)

-- Two complete sequences of longest cuts agree on every boundary.
module Agreement {A : Set} (Q : A → A → Set) where
  open Law Q
  open Prefix {A}
  open Unique {A} using (block-agrees; rest-agrees)
  data Cuts : List A → List (List A) → Set where
    stop : Cuts [] []
    take : ∀ {x xs bs} (g : Longest Connected (x ∷ xs)) → Cuts (Longest.rest g) bs → Cuts (x ∷ xs) (Longest.block g ∷ bs)
  unique : ∀ {xs bs cs} → Cuts xs bs → Cuts xs cs → bs ≡ cs
  unique stop stop = refl
  unique (take g p) (take h q) = cons-eq (block-agrees g h) (unique p (shift (rest-agrees g h) q))
    where shift : ∀ {x y bs} → x ≡ y → Cuts y bs → Cuts x bs
          shift refl w = w
          cons-eq : ∀ {b c : List A} {bs cs} → b ≡ c → bs ≡ cs → b ∷ bs ≡ c ∷ cs
          cons-eq refl refl = refl
