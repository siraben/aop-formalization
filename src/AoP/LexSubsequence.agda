{-# OPTIONS --safe --without-K #-}
module AoP.LexSubsequence where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.GreedyFold using (module Lists)

-- Exercise 7.42. Equal heads preserve dictionary comparison. Thus
-- either subsequence step (keep or drop) on the worse tail can be
-- matched by the same step on the better one. Pick the larger of the
-- two lists and apply the greedy theorem, without yet optimizing the
-- comparison to a test of heads.
module Law {A : Set} (_<_ : A → A → Set)
           (trans : ∀ {a b c} → a < b → b < c → a < c)
           (tri : ∀ a b → (a < b) ⊎ ((a ≡ b) ⊎ (b < a))) where
  data Lex : List A ← List A where
    empty : ∀ {xs} → Lex [] xs
    less : ∀ {a b xs ys} → a < b → Lex (a ∷ xs) (b ∷ ys)
    common : ∀ {a xs ys} → Lex xs ys → Lex (a ∷ xs) (a ∷ ys)

  rid : ∀ xs → Lex xs xs
  rid [] = empty
  rid (x ∷ xs) = common (rid xs)
  chain : ∀ {xs ys zs} → Lex xs ys → Lex ys zs → Lex xs zs
  chain empty q = empty
  chain (less p) (less q) = less (trans p q)
  chain (less p) (common q) = less p
  chain (common p) (less q) = less q
  chain (common p) (common q) = common (chain p q)

  compare : ∀ xs ys → Lex xs ys ⊎ Lex ys xs
  compare [] ys = inl empty
  compare (a ∷ xs) [] = inr empty
  compare (a ∷ xs) (b ∷ ys) with tri a b
  ... | inl p = inl (less p)
  ... | inr (inr q) = inr (less q)
  ... | inr (inl refl) with compare xs ys
  ...   | inl p = inl (common p)
  ...   | inr q = inr (common q)

  data Step : List A ← (A × List A) where
    drop : ∀ {x xs} → Step xs (x , xs)
    keep : ∀ {x xs} → Step (x ∷ xs) (x , xs)
  module G = Lists (λ xs ys → Lex ys xs) (λ p q → chain q p) (λ xs → xs ≡ []) Step
    (λ { p drop → _ , drop , p ; p keep → _ , keep , common p })

  solve : ∀ xs → Σ _ λ ys → G.Greedy ys xs
  solve [] = [] , G.seed (refl , λ { _ refl → empty })
  solve (x ∷ xs) with solve xs
  ... | ys , g with compare ys (x ∷ ys)
  ...   | inl p = _ , G.step g (keep , λ { _ drop → p ; _ keep → rid _ })
  ...   | inr q = _ , G.step g (drop , λ { _ drop → rid _ ; _ keep → q })

  bound : ∀ xs {ys} → Fold (λ zs → zs ≡ []) Step ys xs → Lex ys (fst (solve xs))
  bound xs = G.bound (snd (solve xs))
