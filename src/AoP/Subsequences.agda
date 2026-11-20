{-# OPTIONS --safe --without-K #-}
module AoP.Subsequences where

open import AoP.Prelude
open import AoP.Folds
open import AoP.Relations using (Fold; nil; cons)
open import AoP.Refinement using (Choice; skip; keep)
open import AoP.Naturality using (_++_)
open import AoP.Horner using (map)
open import AoP.Polynomial using (_⊎_; inl; inr)
private variable A B : Set

infix 4 _∈_
data _∈_ (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

merge : (xs ys : List A) {x : A} → (x ∈ xs) ⊎ (x ∈ ys) → x ∈ (xs ++ ys)
merge [] ys (inr q) = q
merge (_ ∷ xs) ys (inl here) = here
merge (_ ∷ xs) ys (inl (there q)) = there (merge xs ys (inl q))
merge (_ ∷ xs) ys (inr q) = there (merge xs ys (inr q))

split : (xs ys : List A) {x : A} → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
split [] ys q = inr q
split (_ ∷ xs) ys here = inl here
split (_ ∷ xs) ys (there q) with split xs ys q
... | inl l = inl (there l)
... | inr r = inr r

image : (f : A → B) {xs : List A} {x : A} → x ∈ xs → f x ∈ map f xs
image f here = here
image f (there q) = there (image f q)

preimage : (f : A → B) (xs : List A) {y : B} → y ∈ map f xs → Σ _ λ x → (x ∈ xs) × (f x ≡ y)
preimage f (x ∷ xs) here = x , here , refl
preimage f (x ∷ xs) (there q) with preimage f xs q
... | z , p , eq = z , there p , eq

-- §5.6. Interpret nondeterministic choice as appending the lists of
-- results, not as deleting duplicates: correctness is about membership.
subs : List A → List (List A)
subs = ⦅ ([] ∷ []) ∣ (λ x yss → map (x ∷_) yss ++ yss) ⦆

Subseq : List A → List A → Set
Subseq = Fold (_≡ []) Choice

complete : ∀ {xs ys : List A} → Subseq ys xs → ys ∈ subs xs
complete (nil refl) = here
complete (cons {x} {xs} skip p) = merge (map (x ∷_) (subs xs)) (subs xs) (inr (complete p))
complete (cons {x} {xs} keep p) = merge (map (x ∷_) (subs xs)) (subs xs) (inl (image (x ∷_) (complete p)))

sound : (xs : List A) {ys : List A} → ys ∈ subs xs → Subseq ys xs
sound [] here = nil refl
sound [] (there ())
sound (x ∷ xs) q with split (map (x ∷_) (subs xs)) (subs xs) q
... | inr p = cons skip (sound xs p)
... | inl p with preimage (x ∷_) (subs xs) p
...   | ys , r , refl = cons keep (sound xs r)
