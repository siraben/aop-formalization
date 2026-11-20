{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.UnzipListLaw where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter05.ListMeet using (Align; nil; cons)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter04.Shunting using (graph)

-- Exercise 5.10 for the list relator. Two independent alignments out
-- of the unzipped lists can be synchronized because both have the
-- length and positions of the original list of pairs.
unzip : ∀ {A B : Set} → List (A × B) → List A × List B
unzip xs = map fst xs , map snd xs
module Law {A B C D : Set} (R : C ← A) (S : D ← B) where
  pair-rel : (C × D) ← (A × B)
  pair-rel y x = R (fst y) (fst x) × S (snd y) (snd x)
  both : (List C × List D) ← (List A × List B)
  both y x = Align R (fst y) (fst x) × Align S (snd y) (snd x)
  project : ∀ {xs ys} → Align pair-rel ys xs → both (unzip ys) (unzip xs)
  project nil = nil , nil
  project (cons (r , s) ps) with project ps
  ... | rs , ss = cons r rs , cons s ss
  rebuild : ∀ xs {cs ds} → Align R cs (map fst xs) → Align S ds (map snd xs) →
            Σ (List (C × D)) λ ys → (unzip ys ≡ (cs , ds)) × Align pair-rel ys xs
  rebuild [] nil nil = [] , refl , nil
  rebuild ((a , b) ∷ xs) (cons {b = c} r rs) (cons {b = d} s ss) with rebuild xs rs ss
  ... | ys , refl , ps = ((c , d) ∷ ys) , refl , cons (r , s) ps

  forward : graph unzip ∘ Align pair-rel ⊆ both ∘ graph unzip
  forward (ys , refl , p) = _ , project p , refl
  backward : both ∘ graph unzip ⊆ graph unzip ∘ Align pair-rel
  backward {a = xs} (_ , (r , s) , refl) = rebuild xs r s
