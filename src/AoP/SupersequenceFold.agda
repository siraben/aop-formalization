{-# OPTIONS --safe --without-K #-}
module AoP.SupersequenceFold where

open import AoP.Prelude
open import AoP.Subsequences using (Subseq)
open import AoP.Refinement using (skip; keep)
open import AoP.Relations using (Fold; nil; cons; _˘)
private variable A : Set

-- Exercise 5.23. To generate supersequences of [], allow any list.
-- For a requested head a, retain an arbitrary prefix before a, then
-- continue with a supersequence of the requested tail. The relation
-- below records the prefix one skipped element at a time.
data InsertHead (a : A) (tail : List A) : List A → Set where
  match : InsertHead a tail (a ∷ tail)
  pass : ∀ {x xs} → InsertHead a tail xs → InsertHead a tail (x ∷ xs)

Super : List A → List A → Set
Super = Fold (λ _ → ⊤) (λ ys p → InsertHead (fst p) (snd p) ys)

prefix : ∀ {a : A} {ys xs tail} → InsertHead a tail ys → Subseq xs tail → Subseq (a ∷ xs) ys
prefix match p = cons keep p
prefix (pass h) p = cons skip (prefix h p)

empty-sub : (ys : List A) → Subseq [] ys
empty-sub [] = nil refl
empty-sub (_ ∷ ys) = cons skip (empty-sub ys)

sound : ∀ {xs ys : List A} → (Super ˘) xs ys → Subseq xs ys
sound {ys = ys} (nil _) = empty-sub ys
sound (cons h p) = prefix h (sound p)

prepend : ∀ {xs ys : List A} {y} → Super ys xs → Super (y ∷ ys) xs
prepend (nil _) = nil tt
prepend (cons h p) = cons (pass h) p

complete : ∀ {xs ys : List A} → Subseq xs ys → (Super ˘) xs ys
complete (nil refl) = nil tt
complete (cons skip p) = prepend (complete p)
complete (cons keep p) = cons match (complete p)
