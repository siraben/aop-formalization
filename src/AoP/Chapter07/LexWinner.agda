{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.LexWinner where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Relations
open import AoP.Chapter07.LexSubsequence using (module Law)
open import AoP.Chapter07.LexHeadFold using (module Head)

module Result {A : Set} (_<_ : A → A → Set) (irr : ∀ a → a < a → ⊥)
              (tr : ∀ {a b c} → a < b → b < c → a < c)
              (tri : ∀ a b → (a < b) ⊎ ((a ≡ b) ⊎ (b < a))) where
  open Law _<_ tr tri
  open Head _<_ tr tri
  private
    absurd : ∀ {X : Set} → ⊥ → X
    absurd ()
    invert : ∀ {a b xs ys} → Lex (a ∷ xs) (b ∷ ys) → (a < b) ⊎ ((a ≡ b) × Lex xs ys)
    invert (less p) = inl p
    invert (common p) = inr (refl , p)

  antisym : ∀ {xs ys} → Lex xs ys → Lex ys xs → xs ≡ ys
  antisym empty empty = refl
  antisym (less p) q with invert q
  ... | inl r = absurd (irr _ (tr p r))
  ... | inr (refl , _) = absurd (irr _ p)
  antisym (common p) q with invert q
  ... | inl r = absurd (irr _ r)
  ... | inr (_ , r) = cong (_ ∷_) (antisym p r)

  Runs = Fold (λ zs → zs ≡ []) Step
  unique : ∀ {xs ys} → Runs ys xs → (∀ zs → Runs zs xs → Lex zs ys) → ys ≡ fst (fast xs)
  unique {xs} run best = antisym (G.bound g run) (best _ (G.feasible g))
    where g = snd (snd (fast xs))

  descending : ∀ {xs ys} → Runs ys xs → (∀ zs → Runs zs xs → Lex zs ys) → Desc ys
  descending {xs} run best rewrite unique run best = fst (snd (fast xs))

  agree : ∀ xs → fst (solve xs) ≡ fst (fast xs)
  agree xs = unique (G.feasible (snd (solve xs))) (λ _ → bound xs)
