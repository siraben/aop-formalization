{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.BagFoldExchange where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.Chapter02.Folds using (⦅_∣_⦆)

-- §5.6. What exactly does the exchange law buy a bag algebra? A fold
-- with commuting insertions is insensitive to every permutation. The
-- converse only forces exchange at states reachable from the seed.
module Law {A B : Set} (seed : B) (add : A → B → B) where
  bagify = ⦅ seed ∣ add ⦆
  ReachableExchange = ∀ a b xs → add a (add b (bagify xs)) ≡ add b (add a (bagify xs))
  Invariant = ∀ {xs ys} → Perm xs ys → bagify xs ≡ bagify ys
  module Suffices (exchange : ReachableExchange) where
    -- Moving a into a later gap requires one adjacent exchange at
    -- each crossed head, followed by the recursive insertion law.
    gap : ∀ {a xs ys} → Insert a xs ys → add a (bagify xs) ≡ bagify ys
    gap front = refl
    gap {a} (later {x} {xs} i) = exchange a x xs ∙ cong (add x) (gap i)
    invariant : Invariant
    invariant empty = refl
    invariant (insert {a} p i) = cong (add a) (invariant p) ∙ gap i
  private
    same : ∀ (xs : List A) → Perm xs xs
    same [] = empty
    same (a ∷ xs) = insert (same xs) front
  necessary : Invariant → ReachableExchange
  necessary law a b xs = law {xs = a ∷ b ∷ xs} {ys = b ∷ a ∷ xs} (insert (same (b ∷ xs)) (later front))

  -- A supplied list representative for every bag extends necessity
  -- to every state. This is the surjectivity premise on bagify.
  everywhere : (∀ state → Σ (List A) (λ xs → bagify xs ≡ state)) → Invariant →
    ∀ a b state → add a (add b state) ≡ add b (add a state)
  everywhere onto law a b state with onto state
  ... | xs , refl = necessary law a b xs
