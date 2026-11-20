{-# OPTIONS --safe --without-K #-}
module AoP.Appendix.ListProduct where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (concat; _++_)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; merge; split; image; preimage)
private variable A B : Set

-- Appendix, cplist. Given a list of menus, enumerate every way of
-- choosing one entry from each. No menus means one empty choice; a
-- single empty menu means no choice. Distinguishing these base cases
-- matters when a product is used to enumerate candidate programs.
choices : List (List A) → List (List A)
choices = ⦅ ([] ∷ []) ∣ (λ menu tails → concat (map (λ x → map (x ∷_) tails) menu)) ⦆

collect : (f : A → List B) {xs : List A} {x : A} {y : B} →
          x ∈ xs → y ∈ f x → y ∈ concat (map f xs)
collect f {x ∷ xs} here q = merge (f x) (concat (map f xs)) (inl q)
collect f {a ∷ xs} (there p) q = merge (f a) (concat (map f xs)) (inr (collect f p q))

locate : (f : A → List B) (xs : List A) {y : B} → y ∈ concat (map f xs) →
         Σ _ λ x → (x ∈ xs) × (y ∈ f x)
locate f (a ∷ xs) m with split (f a) (concat (map f xs)) m
... | inl p = a , here , p
... | inr p with locate f xs p
...   | x , l , r = x , there l , r

-- Pick is the specification, independent of any enumeration order.
data Pick {A : Set} : List A → List (List A) → Set where
  none : Pick [] []
  one : ∀ {a as m ms} → a ∈ m → Pick as ms → Pick (a ∷ as) (m ∷ ms)

complete : ∀ {as : List A} {ms} → Pick as ms → as ∈ choices ms
complete none = here
complete (one {a} {ms = ms} p q) = collect (λ x → map (x ∷_) (choices ms)) p (image (a ∷_) (complete q))

sound : (ms : List (List A)) {as : List A} → as ∈ choices ms → Pick as ms
sound [] here = none
sound [] (there ())
sound (m ∷ ms) q with locate (λ x → map (x ∷_) (choices ms)) m q
... | a , p , r with preimage (a ∷_) (choices ms) r
...   | as , tail , refl = one p (sound ms tail)
