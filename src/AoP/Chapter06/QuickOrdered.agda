{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickOrdered where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter06.QuickPermutation using (flatten-perm; preserves)
import AoP.Chapter05.Permutations as P
open import AoP.Chapter06.Selection using (Lower; below; empty; weaken; Remove; head; past)
open import AoP.Chapter06.SelectionSort using (Sorted; cons; nil; length; Result; Perm; finish)
open import AoP.Chapter06.InsertionSort using (carry; lower-add)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; rid)
open import Agda.Builtin.Nat using (Nat)

-- §6.6. Each split compares every key on either side with the pivot.
-- Recursive sorting merely permutes those keys, so the bounds still hold
-- when we join the two sorted lists with the pivot between them.
data Upper (p : Nat) : List Nat → Set where
  end : Upper p []
  next : ∀ {x xs} → x ≤ p → Upper p xs → Upper p (x ∷ xs)

bounds : ∀ {p xs l r} → Split p xs l r → Upper p l × Lower p r
bounds (pivot p) = end , empty
bounds (left le s) = next le (fst (bounds s)) , snd (bounds s)
bounds (right ge s) = fst (bounds s) , below ge (snd (bounds s))

remove : ∀ {a xs ys} → P.Insert a xs ys → Remove a ys xs
remove P.front = head
remove (P.later i) = past (remove i)

upper-add : ∀ {a p xs ys} → a ≤ p → Upper p xs → P.Insert a xs ys → Upper p ys
upper-add le b P.front = next le b
upper-add le (next x b) (P.later i) = next x (upper-add le b i)

upper-perm : ∀ {p xs ys} → P.Perm xs ys → Upper p xs → Upper p ys
upper-perm P.empty end = end
upper-perm (P.insert q pos) (next le b) = upper-add le (upper-perm q b) pos

lower-perm : ∀ {p xs ys} → P.Perm xs ys → Lower p xs → Lower p ys
lower-perm P.empty empty = empty
lower-perm (P.insert q pos) (below le b) = lower-add le (lower-perm q b) (remove pos)

append-bound : ∀ {p xs ys} → Lower p xs → Lower p ys → Lower p (xs ++ ys)
append-bound empty b = b
append-bound (below le rest) b = below le (append-bound rest b)

join : ∀ {p l r} → Upper p l → Lower p r → Sorted l → Sorted r → Sorted (l ++ (p ∷ r))
join end ge nil rs = cons ge rs
join (next le up) ge (cons lb ls) rs =
  cons (append-bound lb (below le (weaken le ge))) (join up ge ls rs)

ordered : ∀ {xs} (t : Tree xs) → Sorted (flatten t)
ordered null = nil
ordered (fork p s l r) = join (upper-perm (flatten-perm l) (fst (bounds s)))
                             (lower-perm (flatten-perm r) (snd (bounds s))) (ordered l) (ordered r)

convert : ∀ {xs ys} → P.Perm xs ys → Perm xs ys
convert P.empty = finish
convert (P.insert q pos) = carry (remove pos) (convert q)

-- Same public specification as selection sort and insertion sort.
certified : ∀ xs → Result xs
certified xs = quicksort xs , convert (preserves xs) , ordered (unfold (length xs) xs (rid _))
