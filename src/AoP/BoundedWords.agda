{-# OPTIONS --safe --without-K #-}
module AoP.BoundedWords where

open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.Naturality using (concat)
open import AoP.Subsequences using (_∈_; here; there; image)
open import AoP.ListProduct using (collect)
open import AoP.CompressionGrowth using (len)
open import AoP.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §9.4, finite search infrastructure. Given a list of possible tokens
-- and a length limit, enumerate every word up to that length. A word
-- may stop early, including before emitting its first token.
module Words {A : Set} (tokens : List A) where
  words : Nat → List (List A)
  words zero = [] ∷ []
  words (suc k) = [] ∷ concat (map (λ a → map (a ∷_) (words k)) tokens)

  data Over : List A → Set where
    empty : Over []
    extend : ∀ {a xs} → a ∈ tokens → Over xs → Over (a ∷ xs)

  complete : ∀ {xs} k → len xs ≤ k → Over xs → xs ∈ words k
  complete zero _ empty = here
  complete (suc k) _ empty = here
  complete (suc k) (s≤ within) (extend {a} member tail) =
    there (collect (λ x → map (x ∷_) (words k)) member (image (a ∷_) (complete k within tail)))

-- Store precisely the indices strictly below n; neither offsets nor
-- length-minus-one fields of a successful pointer need larger indices.
indices : Nat → List Nat
indices zero = []
indices (suc k) = zero ∷ map suc (indices k)

index-member : ∀ i n → suc i ≤ n → i ∈ indices n
index-member zero (suc n) _ = here
index-member (suc i) (suc n) (s≤ p) = there (image suc (index-member i n p))
