{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedMaximum where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.ConnectedBlock using (module Law)

-- Exercise 8.14, optimized extension test. Cache a greatest member
-- of the current nonempty block. Under the common-upper-bound law,
-- comparing the newcomer with that one member decides whether the
-- entire enlarged block is connected, and updates the cached maximum.
module Test {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
            (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
            (fork : ∀ {a b c} → Q a c → Q b c → Q a b ⊎ Q b a) where
  open Law Q
  Greatest : List A → A → Set
  Greatest xs m = (m ∈ xs) × (∀ b → b ∈ xs → Q b m)

  necessary : ∀ {a xs m} → Greatest xs m → Connected (a ∷ xs) → Q a m ⊎ Q m a
  necessary (member , _) c = c _ _ here (there member)

  update : ∀ a xs m → Connected xs → Greatest xs m → Q a m ⊎ Q m a →
           Connected (a ∷ xs) × (Σ A λ n → Greatest (a ∷ xs) n)
  update a xs m c (member , bound) (inl am) =
    extend (rr a) (λ b xb → fork am (bound b xb)) c ,
    m , there member , (λ { _ here → am ; b (there xb) → bound b xb })
  update a xs m c (member , bound) (inr ma) =
    extend (rr a) (λ b xb → inr (tr (bound b xb) ma)) c ,
    a , here , (λ { _ here → rr a ; b (there xb) → tr (bound b xb) ma })
