{-# OPTIONS --safe --without-K #-}
module AoP.LongestConnectedBlock where

open import AoP.Prelude
open import AoP.ConnectedBlock using (module Law)
open import AoP.LongestPrefix using (module Prefix)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)

-- 8.14. Test all comparisons with a new head, retaining the exact
-- offending pair on a negative branch. Prefix closure then permits
-- the longest-prefix scan to stop at the first failed extension.
module Scan {A : Set} (Q : A → A → Set) (self : ∀ x → Q x x)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Law Q
  open Prefix {A}
  Cross : A → List A → Set
  Cross x xs = ∀ y → y ∈ xs → Q x y ⊎ Q y x
  cross? : ∀ x xs → Dec (Cross x xs)
  cross? x [] = inl (λ y ())
  cross? x (z ∷ zs) with test x z | cross? x zs
  ... | inl cmp | inl rest = inl λ { _ here → cmp ; y (there m) → rest y m }
  ... | inr no | _ = inr λ ok → no (ok z here)
  ... | _ | inr no = inr λ ok → no (λ y m → ok y (there m))
  valid? : ∀ xs → Dec (Connected xs)
  valid? [] = inl (λ x y ())
  valid? (x ∷ xs) with cross? x xs | valid? xs
  ... | inl cmp | inl ok = inl (extend (self x) cmp ok)
  ... | inr no | _ = inr λ ok → no (λ y m → ok x y here (there m))
  ... | _ | inr no = inr λ ok → no (λ y z m n → ok y z (there m) (there n))
  include : ∀ {xs ys x} → xs ≼ ys → x ∈ xs → x ∈ ys
  include (cons _) here = here
  include (cons p) (there m) = there (include p m)
  first : ∀ xs → Longest Connected xs
  first xs = scan xs Connected (λ x y ()) valid? (λ p ok x y m n → ok x y (include p m) (include p n))
