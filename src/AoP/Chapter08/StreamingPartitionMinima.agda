{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.StreamingPartitionMinima where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_)
open import AoP.Chapter08.ConnectedPartitionFusion using (module Fusion)
open import AoP.Chapter08.StreamingCutSequence using (module Proof)
open import AoP.Chapter08.ConnectedReverseCut using (module Restore)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Chapter08.Thinning using (Min)

-- The fused program may choose a different representative among tied
-- minima. Relate its actual output to the reference blocks in order.
module EndToEnd {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {a b c} → Q a b → Q b c → Q a c) (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Fusion Q rr tr test
  open Proof Q rr tr test using (saved; blocks; text; agrees; module Ref)
  open Restore Q
  data Minima : List (List A) → List A → Set where
    none : Minima [] []
    pick : ∀ {b bs a as} → Min Q a (λ x → x ∈ b) → Minima bs as → Minima (b ∷ bs) (a ∷ as)
  output : Snoc A → List A → List A
  output ε tail = tail
  output (as ▻ a) tail = output as (a ∷ tail)
  least : ∀ b → Min Q (Block.m b) (λ x → x ∈ rev (Block.xs b))
  least b = forward _ (Block.member b) , λ x m → Block.lower b (backward _ m)
  saved-minima : ∀ ds {bs as} → Minima bs as → Minima (saved ds bs) (output (minima ds) as)
  saved-minima ε ms = ms
  saved-minima (ds ▻ b) ms = saved-minima ds (pick (least b) ms)
  state-minima : ∀ s → Minima (blocks s) (output (finish Block.m (erase s)) [])
  state-minima empty = none
  state-minima (active ds b) = saved-minima ds (pick (least b) none)
  certified : ∀ t → Minima (Ref.block-list (Ref.Result.partition (Ref.solve (text t)))) (output (thinlist t) [])
  certified t = change (agrees t) (cong (λ s → output (finish Block.m s) []) (fusion t)) (state-minima (partition t))
    where change : ∀ {bs cs as ds} → bs ≡ cs → as ≡ ds → Minima bs as → Minima cs ds
          change refl refl proof = proof
