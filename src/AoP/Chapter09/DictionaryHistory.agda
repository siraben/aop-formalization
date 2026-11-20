{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryHistory where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)

-- History is built newest-first. When a letter is appended, the only
-- new strict prefix is the previous whole text. Use actual list
-- equality rather than a comparison of lengths to retrieve its row.
module Prefix {A : Set} where
  Proper : List A → List A → Set
  Proper xs ys = Σ A λ a → Σ (List A) λ zs → xs ++ (a ∷ zs) ≡ ys
  nonempty : ∀ (xs : List A) a zs → xs ++ (a ∷ zs) ≡ [] → {B : Set} → B
  nonempty [] a zs ()
  nonempty (_ ∷ xs) a zs ()
  previous : ∀ xs ys a → Proper xs (ys ++ (a ∷ [])) → (xs ≡ ys) ⊎ Proper xs ys
  previous [] [] a p = inl refl
  previous [] (b ∷ ys) a p = inr (b , ys , refl)
  previous (x ∷ xs) [] a (b , zs , eq) = nonempty xs b zs (tail eq)
    where tail : ∀ {x y : A} {u v : List A} → x ∷ u ≡ y ∷ v → u ≡ v
          tail refl = refl
  previous (x ∷ xs) (y ∷ ys) a (b , zs , eq) with heads eq | tails eq
    where heads : ∀ {x y : A} {u v : List A} → x ∷ u ≡ y ∷ v → x ≡ y
          heads refl = refl
          tails : ∀ {x y : A} {u v : List A} → x ∷ u ≡ y ∷ v → u ≡ v
          tails refl = refl
  ... | refl | tail with previous xs ys a (b , zs , tail)
  ... | inl refl = inl refl
  ... | inr (d , us , sub) = inr (d , us , cong (x ∷_) sub)

  module Rows (Entry : List A → Set) where
    Row = Σ (List A) Entry
    Covers : List Row → List A → Set
    Covers rs ys = ∀ xs → Proper xs ys → Σ (Entry xs) λ e → (xs , e) ∈ rs
    start : Covers [] []
    start xs (a , zs , eq) = nonempty xs a zs eq
    advance : ∀ {rs ys} (e : Entry ys) a → Covers rs ys → Covers ((ys , e) ∷ rs) (ys ++ (a ∷ []))
    advance {rs} {ys} e a covers xs sub with previous xs ys a sub
    ... | inl refl = e , here
    ... | inr p = let old , member = covers xs p in old , there member
