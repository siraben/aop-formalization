{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DisjointGreedyBranches where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.RelationalSums using (_⊕_; left; right)
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter09.DisjointFibres using (module Law)

-- §10.1, Proposition 10.1. First minimize the legal split, then
-- evaluate that split. A range test decides which smaller minimum
-- problem to solve. The result relations U and Z may be partial.
module Branch {A B C D : Set} (V : C ← A) (W : C ← B) (U : D ← A) (Z : D ← B)
  (Q : A ← A) (S : B ← B) where
  open Law V W using (Left; Disjoint; fibre)
  eval : D ← (A ⊎ B)
  eval d (inl a) = U d a
  eval d (inr b) = Z d b
  Whole : D ← C
  Whole d c = Σ (A ⊎ B) λ t → Min (Q ⊕ S) t (fibre c) × eval d t
  L : D ← C
  L d c = Σ A λ a → Min Q a (V c) × U d a
  R : D ← C
  R d c = Σ B λ b → Min S b (W c) × Z d b

  unleft : ∀ {a b} → (Q ⊕ S) (inl a) (inl b) → Q a b
  unleft (left q) = q
  unright : ∀ {a b} → (Q ⊕ S) (inr a) (inr b) → S a b
  unright (right s) = s
  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()

  module Select (dis : Disjoint) (test : ∀ c → Left c ⊎ (Left c → ⊥)) where
    Choice : D ← C
    Choice d c with test c
    ... | inl _ = L d c
    ... | inr _ = R d c
    forward : ∀ d c → Whole d c → Choice d c
    forward d c (inl a , (va , wins) , out) with test c
    ... | inl _ = a , (va , (λ b vb → unleft (wins (inl b) vb))) , out
    ... | inr no = absurd (no (a , va))
    forward d c (inr b , (wb , wins) , out) with test c
    ... | inl yes = absurd (dis c yes (b , wb))
    ... | inr _ = b , (wb , (λ a wa → unright (wins (inr a) wa))) , out

    -- Rebuild a whole-fibre minimum. A rival with the same tag loses
    -- by the branch minimum; an opposite-tag rival cannot be legal.
    backward : ∀ d c → Choice d c → Whole d c
    backward d c choice with test c | choice
    ... | inl yes | a , (va , wins) , out = inl a , (va , (λ where
      (inl b) vb → left (wins b vb)
      (inr b) wb → absurd (dis c yes (b , wb)))) , out
    ... | inr no | b , (wb , wins) , out = inr b , (wb , (λ where
      (inl a) va → absurd (no (a , va))
      (inr a) wa → right (wins a wa))) , out
