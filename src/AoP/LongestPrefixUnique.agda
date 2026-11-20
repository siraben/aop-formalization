{-# OPTIONS --safe --without-K #-}
module AoP.LongestPrefixUnique where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.LongestPrefix using (module Prefix)

-- A streaming cut and a scanning cut can carry different proofs of
-- maximality. Their observable block and suffix nevertheless agree.
module Unique {A : Set} where
  open Prefix {A}
  tail-prefix : ∀ {a b xs ys} → (a ∷ xs) ≼ (b ∷ ys) → xs ≼ ys
  tail-prefix (cons q) = q
  antisym : ∀ {xs ys} → xs ≼ ys → ys ≼ xs → xs ≡ ys
  antisym nil nil = refl
  antisym (cons p) q = cong (_ ∷_) (antisym p (tail-prefix q))
  initial : ∀ xs ys → xs ≼ (xs ++ ys)
  initial [] ys = nil
  initial (x ∷ xs) ys = cons (initial xs ys)
  prefix-of : ∀ {P xs} (g : Longest P xs) → Longest.block g ≼ xs
  prefix-of (result bs rs refl _ _) = initial bs rs
  block-agrees : ∀ {P xs} (g h : Longest P xs) → Longest.block g ≡ Longest.block h
  block-agrees g h = antisym (Longest.dominates h (prefix-of g) (Longest.fits g))
                              (Longest.dominates g (prefix-of h) (Longest.fits h))
  private
    cancel : ∀ xs {ys zs} → xs ++ ys ≡ xs ++ zs → ys ≡ zs
    cancel [] eq = eq
    cancel (x ∷ xs) eq = cancel xs (tails eq)
      where tails : ∀ {a b : A} {ys zs : List A} → a ∷ ys ≡ b ∷ zs → ys ≡ zs
            tails refl = refl
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
  rest-agrees : ∀ {P xs} (g h : Longest P xs) → Longest.rest g ≡ Longest.rest h
  rest-agrees (result bs rs eq ok dom) (result cs ss eq′ ok′ dom′) with block-agrees (result bs rs eq ok dom) (result cs ss eq′ ok′ dom′)
  ... | refl = cancel bs (eq ∙ rev eq′)
