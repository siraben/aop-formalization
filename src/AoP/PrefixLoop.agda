{-# OPTIONS --safe --without-K #-}
module AoP.PrefixLoop where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_; foldl)

-- Exercise 9.13. Accumulate h on each successive nonempty prefix.
-- The empty input contributes no step. Appending one item appends
-- exactly one new prefix, so only the last accumulator update is new.
module Law {A B C D : Set} (g : A → B) (h : Snoc C → D) (f : B → D → B) where
  prefixes : Snoc C → Snoc (Snoc C)
  prefixes ε = ε
  prefixes (xs ▻ x) = prefixes xs ▻ (xs ▻ x)

  mapped : Snoc (Snoc C) → Snoc D
  mapped = foldl ε (λ ds xs → ds ▻ h xs)

  spec : A → Snoc C → B
  spec a xs = foldl (g a) f (mapped (prefixes xs))

  module Characterise (k : A → Snoc C → B) where
    Same = ∀ a xs → k a xs ≡ spec a xs
    Base = ∀ a → k a ε ≡ g a
    Step = ∀ a xs x → k a (xs ▻ x) ≡ f (k a xs) (h (xs ▻ x))
    private
      back : ∀ {x y : B} → x ≡ y → y ≡ x
      back refl = refl
    necessary : Same → Base × Step
    necessary eq = (λ a → eq a ε) , λ a xs x → eq a (xs ▻ x) ∙ cong (λ b → f b (h (xs ▻ x))) (back (eq a xs))
    sufficient : Base → Step → Same
    sufficient base step a ε = base a
    sufficient base step a (xs ▻ x) = step a xs x ∙ cong (λ b → f b (h (xs ▻ x))) (sufficient base step a xs)
