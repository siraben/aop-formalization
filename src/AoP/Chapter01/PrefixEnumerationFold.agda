{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.PrefixEnumerationFold where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)
open import AoP.Chapter01.Naturality using (inits)

-- §1.6. Store all the prefixes already generated. The last entry is
-- the entire input seen so far; extend just that entry and append it.
module Law {A : Set} where
  extend : Snoc (Snoc A) → A → Snoc (Snoc A)
  extend ε a = ε ▻ (ε ▻ a)  -- unreachable from the singleton seed
  extend (ps ▻ p) a = (ps ▻ p) ▻ (p ▻ a)

  prefixes : Snoc A → Snoc (Snoc A)
  prefixes = foldl (ε ▻ ε) extend

  -- Expose the final prefix so the fold step selects its second clause.
  ends : ∀ xs → Σ (Snoc (Snoc A)) λ ps → inits xs ≡ (ps ▻ xs)
  ends ε = ε , refl
  ends (xs ▻ x) = inits xs , refl

  correct : ∀ xs → prefixes xs ≡ inits xs
  correct ε = refl
  correct (xs ▻ x) rewrite correct xs with ends xs
  ... | ps , eq rewrite eq = refl

  three : ∀ (a b c : A) → prefixes (ε ▻ a ▻ b ▻ c) ≡
          ε ▻ ε ▻ (ε ▻ a) ▻ (ε ▻ a ▻ b) ▻ (ε ▻ a ▻ b ▻ c)
  three a b c = refl
