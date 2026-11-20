{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedPartitionFusion where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter08.LongestConnectedBlock using (module Scan)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)

-- 8.14. Process letters left to right. The active block is stored
-- newest first for its comparability test. On closing a block retain
-- only its minimum, rather than storing all the completed blocks.
module Fusion {A : Set} (Q : A → A → Set) (self : ∀ x → Q x x)
  (trans : ∀ {x y z} → Q x y → Q y z → Q x z)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Scan Q self test using (Cross; cross?)
  record Block : Set where
    constructor block
    field xs : List A
          m : A
          member : m ∈ xs
          lower : ∀ {x} → x ∈ xs → Q m x
  open Block
  one : A → Block
  one a = block (a ∷ []) a here λ { here → self a ; (there ()) }
  extend : ∀ a b → Cross a (xs b) → Block
  extend a b cmp with cmp (m b) (member b)
  ... | inl le = block (a ∷ xs b) a here λ { here → self a ; (there p) → trans le (lower b p) }
  ... | inr le = block (a ∷ xs b) (m b) (there (member b)) λ { here → le ; (there p) → lower b p }
  data State (C : Set) : Set where
    empty : State C
    active : Snoc C → Block → State C
  advance : ∀ {C} → (Block → C) → State C → A → State C
  advance save empty a = active ε (one a)
  advance save (active done b) a with cross? a (xs b)
  ... | inl ok = active done (extend a b ok)
  ... | inr _ = active (done ▻ save b) (one a)
  minima : Snoc Block → Snoc A
  minima ε = ε
  minima (bs ▻ b) = minima bs ▻ m b
  erase : State Block → State A
  erase empty = empty
  erase (active bs b) = active (minima bs) b
  commute : ∀ s a → erase (advance (λ x → x) s a) ≡ advance m (erase s) a
  commute empty a = refl
  commute (active bs b) a with cross? a (xs b)
  ... | inl ok = refl
  ... | inr _ = refl
  partition = foldl empty (advance (λ x → x))
  fused = foldl empty (advance m)
  fusion : ∀ t → erase (partition t) ≡ fused t
  fusion ε = refl
  fusion (t ▻ a) = commute (partition t) a ∙ cong (λ s → advance m s a) (fusion t)
  finish : ∀ {C} → (Block → C) → State C → Snoc C
  finish save empty = ε
  finish save (active ds b) = ds ▻ save b
  close : ∀ s → minima (finish (λ x → x) s) ≡ finish m (erase s)
  close empty = refl
  close (active ds b) = refl
  thinlist = λ t → finish m (fused t)
  equation : ∀ t → minima (finish (λ x → x) (partition t)) ≡ thinlist t
  equation t = close (partition t) ∙ cong (finish m) (fusion t)
