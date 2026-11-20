{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickEquation where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter06.SelectionSort using (length)
open import AoP.Common.NatOrder using (_≤_; rid; chain; s≤)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc)

-- §6.6. Removing the intermediate tree gives the usual recursive
-- equation. Each child in `unfold` inherits its parent's remaining
-- budget, whereas a fresh call of `quicksort` starts at the child's
-- own length. Prove their outputs equal without identifying the proofs
-- of either length bound.
join : Nat → List Nat → List Nat → List Nat
join p l r = l ++ (p ∷ r)

join-cong : ∀ p {a b c d} → a ≡ b → c ≡ d → join p a c ≡ join p b d
join-cong p refl refl = refl

independent : ∀ n m xs (a : length xs ≤ n) (b : length xs ≤ m) →
              flatten (unfold n xs a) ≡ flatten (unfold m xs b)
independent n m [] a b = refl
independent (suc n) (suc m) (x ∷ xs) (s≤ a) (s≤ b) with split x xs
... | p , l , r , s with smaller s
...   | s≤ lb , s≤ rb = join-cong p (independent n m l (chain lb a) (chain lb b))
                                    (independent n m r (chain rb a) (chain rb b))

children : ∀ x xs → List Nat
children x xs with split x xs
... | p , l , r , s = join p (quicksort l) (quicksort r)

empty-case : quicksort [] ≡ []
empty-case = refl

fork-case : ∀ x xs → quicksort (x ∷ xs) ≡ children x xs
fork-case x xs with split x xs
... | p , l , r , s with smaller s
...   | s≤ lb , s≤ rb = join-cong p (independent _ _ l (chain lb (rid _)) (rid _))
                                    (independent _ _ r (chain rb (rid _)) (rid _))
