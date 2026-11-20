{-# OPTIONS --safe --without-K #-}
module AoP.CachedBlockExtrema where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.CachedConnectedFold using (module Fold)
open import AoP.ConnectedBlock using (module Law)
open import AoP.Thinning using (Min)

-- Ghost blocks document the compact fold; they are absent from run.
-- The two active extrema occur in the block maintained by the proof,
-- even when comparisons tie. Closing a block resets the witness.
module Check {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {x y z} → Q x y → Q y z → Q x z)
  (fork : ∀ {x y z} → Q x z → Q y z → Q x y ⊎ Q y x)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Fold Q rr tr fork test
  open Law Q
  record Bounds (xs : List A) (lo hi : A) : Set where
    constructor bounds
    field connected : Connected xs
          least : Min Q lo (λ x → x ∈ xs)
          greatest : (hi ∈ xs) × (∀ x → x ∈ xs → Q x hi)
  singleton : ∀ a → Bounds (a ∷ []) a a
  singleton a = bounds (extend (rr a) (λ x ()) (λ x y ())) (here , λ { _ here → rr a ; _ (there ()) }) (here , λ { _ here → rr a ; _ (there ()) })
  data Witness : State → Set where
    vacant : Witness empty
    current : ∀ {ds lo hi le} xs → Bounds xs lo hi → Witness (active ds lo hi le)
  advance : ∀ s a → Witness s → Witness (step s a)
  advance empty a vacant = current (a ∷ []) (singleton a)
  advance (active ds lo hi le) a (current xs (bounds ok (l , low) (h , high))) with test a hi
  ... | inr no = current (a ∷ []) (singleton a)
  ... | inl (inr ha) = current (a ∷ xs) (bounds (extend (rr a) (λ x m → inr (tr (high x m) ha)) ok)
    (there l , (λ { _ here → tr le ha ; x (there m) → low x m }))
    (here , (λ { _ here → rr a ; x (there m) → tr (high x m) ha })))
  ... | inl (inl ah) with fork ah le
  ...   | inl al = current (a ∷ xs) (bounds (extend (rr a) (λ x m → fork ah (high x m)) ok)
    (here , (λ { _ here → rr a ; x (there m) → tr al (low x m) }))
    (there h , (λ { _ here → ah ; x (there m) → high x m })))
  ...   | inr la = current (a ∷ xs) (bounds (extend (rr a) (λ x m → fork ah (high x m)) ok)
    (there l , (λ { _ here → la ; x (there m) → low x m }))
    (there h , (λ { _ here → ah ; x (there m) → high x m })))
  invariant : ∀ t → Witness (run t)
  invariant ε = vacant
  invariant (t ▻ a) = advance (run t) a (invariant t)
