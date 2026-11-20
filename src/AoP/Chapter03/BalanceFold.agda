{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.BalanceFold where

open import AoP.Common.Prelude
open import AoP.Chapter03.Steep using (_and_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _<_)
open import Agda.Builtin.Bool using (Bool; true)

-- Exercise 3.5. At a node with subtree sizes n and m, test whether
-- n/(n+m+1) lies in [1/3,2/3]. Both endpoints are inclusive. Compare
-- integer cross-products to avoid rounding and division. Keep the size
-- of an empty tree explicit: it affects which trees satisfy this test.
data Tree (A : Set) : Set where
  null : Tree A
  node : Tree A → A → Tree A → Tree A

fits : Nat → Nat → Bool
fits n m = (total < suc (3 * n)) and ((3 * n) < suc (2 * total))
  where total = suc (n + m)

module Check {A : Set} (empty-size : Nat) where
  size : Tree A → Nat
  size null = empty-size
  size (node l _ r) = suc (size l + size r)

  balanced : Tree A → Bool
  balanced null = true
  balanced (node l _ r) = fits (size l) (size r) and (balanced l and balanced r)

  combine : Nat × Bool → Nat × Bool → Nat × Bool
  combine (n , b) (m , c) = suc (n + m) , (fits n m and (b and c))
  scan : Tree A → Nat × Bool
  scan null = empty-size , true
  scan (node l _ r) = combine (scan l) (scan r)

  invariant : ∀ t → scan t ≡ (size t , balanced t)
  invariant null = refl
  invariant (node l a r) = begin
    combine (scan l) (scan r) ≡⟨ cong (λ p → combine p (scan r)) (invariant l) ⟩
    combine (size l , balanced l) (scan r) ≡⟨ cong (combine (size l , balanced l)) (invariant r) ⟩
    (size (node l a r) , balanced (node l a r)) ∎

  correct : ∀ t → snd (scan t) ≡ balanced t
  correct t = cong snd (invariant t)

-- Local tests of both boundaries: 1/(1+1+1) and 2/(2+0+1).
endpoints : (fits 1 1 ≡ true) × (fits 2 0 ≡ true)
endpoints = refl , refl
