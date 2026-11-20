{-# OPTIONS --safe --without-K #-}
module AoP.PostorderSort where

open import AoP.Prelude
open import AoP.PreorderSort using (Tree; null; fork)
open import AoP.Selection using (Remove; head; past; Lower; below; empty)
open import AoP.SelectionSort using (Perm; finish; Sorted; nil; cons; Result)
open import AoP.InsertionSort using (carry)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; compare; chain)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 6.27. Postorder puts the root last, so it must be a maximum.
-- Maintain a left spine with its largest key at the root. When inserting
-- a larger key, make it the new root; otherwise insert into the old
-- root's child. For [2,3,1], inserting 2 into the spine [1,3] descends
-- past 3 and installs 2 above 1, giving the traversal [1,2,3].
post : Tree → List Nat
post null = []
post (fork l a r) = post l ++ (post r ++ (a ∷ []))

at-end : ∀ a xs → Remove a (xs ++ (a ∷ [])) xs
at-end a [] = head
at-end a (x ∷ xs) = past (at-end a xs)

keep-end : ∀ {a xs ys} b → Remove a ys xs → Remove a (ys ++ (b ∷ [])) (xs ++ (b ∷ []))
keep-end b head = head
keep-end b (past p) = past (keep-end b p)

-- Bound each spine key by a ceiling; adding a key below that ceiling
-- preserves the bound, independently of the insertion position.
data Capped (b : Nat) : List Nat → Set where
  nil : Capped b []
  cons : ∀ {a xs} → a ≤ b → Capped b xs → Capped b (a ∷ xs)

snoc-cap : ∀ {a b xs} → Capped a xs → a ≤ b → Capped b (xs ++ (a ∷ []))
snoc-cap nil le = cons le nil
snoc-cap (cons ax tail) le = cons (chain ax le) (snoc-cap tail le)

data Good : Tree → Set where
  base : Good null
  maximum : ∀ {t} a → Good t → Capped a (post t) → Good (fork t a null)

cap-add : ∀ {a b xs ys} → a ≤ b → Remove a ys xs → Capped b xs → Capped b ys
cap-add le head c = cons le c
cap-add le (past p) (cons x c) = cons x (cap-add le p c)

insert : ∀ {t} a → Good t → Σ Tree λ u → Good u × Remove a (post u) (post t)
insert a base = _ , maximum a base nil , head
insert a (maximum {t} b g c) with compare a b
... | inr ba = _ , maximum a (maximum b g c) (snoc-cap c ba) , at-end a _
... | inl ab with insert a g
...   | u , h , rem = _ , maximum b h (cap-add ab rem c) , keep-end b rem

snoc-lower : ∀ {a b xs} → Lower a xs → a ≤ b → Lower a (xs ++ (b ∷ []))
snoc-lower empty le = below le empty
snoc-lower (below x tail) le = below x (snoc-lower tail le)

snoc-sorted : ∀ {a xs} → Capped a xs → Sorted xs → Sorted (xs ++ (a ∷ []))
snoc-sorted nil nil = cons empty nil
snoc-sorted (cons le c) (cons lb sorted) = cons (snoc-lower lb le) (snoc-sorted c sorted)

ordered : ∀ {t} → Good t → Sorted (post t)
ordered base = nil
ordered (maximum a g c) = snoc-sorted c (ordered g)

build : ∀ xs → Σ Tree λ t → Good t × Perm xs (post t)
build [] = null , base , finish
build (a ∷ xs) with build xs
... | t , g , p with insert a g
...   | u , h , rem = u , h , carry rem p

sort : ∀ xs → Result xs
sort xs with build xs
... | t , g , p = post t , p , ordered g

example : fst (sort (2 ∷ 3 ∷ 1 ∷ [])) ≡ 1 ∷ 2 ∷ 3 ∷ []
example = refl
