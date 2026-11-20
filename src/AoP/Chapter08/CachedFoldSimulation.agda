{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.CachedFoldSimulation where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Chapter05.Subsequences using (here; there)
import AoP.Chapter08.CachedConnectedFold as Cache
import AoP.Chapter08.ConnectedPartitionFusion as Stream
import AoP.Chapter08.StreamingCutSequence as Cuts
import AoP.Chapter08.StreamingPartitionMinima as End
open import AoP.Chapter08.ConnectedReverseCut using (module Restore)
open import AoP.Chapter08.LongestConnectedBlock using (module Scan)
open import AoP.Chapter08.CachedBlockExtrema using (module Check)
open import AoP.Chapter04.Complement using (⊥)

module Proof {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {x y z} → Q x y → Q y z → Q x z)
  (fork : ∀ {x y z} → Q x z → Q y z → Q x y ⊎ Q y x)
  (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  module C = Cache.Fold Q rr tr fork test
  module S = Stream.Fusion Q rr tr test
  open Cuts.Proof Q rr tr test using (saved; blocks; text; agrees; grow-xs; module Ref)
  open End.EndToEnd Q rr tr test using (Minima; none; pick; output)
  open Restore Q
  open Scan Q rr test using (cross?)
  open Check Q rr tr fork test using (Bounds; bounds; singleton)
  open import AoP.Chapter08.ConnectedBlock using (module Law)
  open Law Q using (extend)
  open S.Block using (xs)
  data Sync : S.State S.Block → C.State → Set where
    nil : Sync S.empty C.empty
    row : ∀ {ds b ms lo hi le} → Bounds (xs b) lo hi →
      (∀ bs as → Minima bs as → Minima (saved ds bs) (output ms as)) →
      Sync (S.active ds b) (C.active ms lo hi le)
  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()
  step : ∀ s c a → Sync s c → Sync (S.advance (λ x → x) s a) (C.step c a)
  step S.empty C.empty a nil = row (singleton a) (λ _ _ m → m)
  step (S.active ds b) (C.active ms lo hi le) a (row (bounds ok (l , low) (h , high)) prev) with cross? a (xs b) | test a hi
  ... | inr bad | inr no = row (singleton a) (λ bs as m → prev _ _ (pick (forward (xs b) l , (λ x p → low x (backward (xs b) p))) m))
  ... | inl cmp | inr no = absurd (no (cmp hi h))
  ... | inr no | inl (inr ha) = absurd (no (λ x p → inr (tr (high x p) ha)))
  ... | inr no | inl (inl ah) = absurd (no (λ x p → fork ah (high x p)))
  ... | inl cmp | inl (inr ha) = row (restore (bounds (extend (rr a) cmp ok) (there l , (λ { _ here → tr le ha ; x (there p) → low x p })) (here , (λ { _ here → rr a ; x (there p) → tr (high x p) ha })))) prev
    where restore : ∀ {lo hi} → Bounds (a ∷ xs b) lo hi → Bounds (xs (S.extend a b cmp)) lo hi
          restore p rewrite grow-xs a b cmp = p
  ... | inl cmp | inl (inl ah) with fork ah le
  ...   | inl al = row (restore (bounds (extend (rr a) cmp ok) (here , (λ { _ here → rr a ; x (there p) → tr al (low x p) })) (there h , (λ { _ here → ah ; x (there p) → high x p })))) prev
    where restore : ∀ {lo hi} → Bounds (a ∷ xs b) lo hi → Bounds (xs (S.extend a b cmp)) lo hi
          restore p rewrite grow-xs a b cmp = p
  ...   | inr la = row (restore (bounds (extend (rr a) cmp ok) (there l , (λ { _ here → la ; x (there p) → low x p })) (there h , (λ { _ here → ah ; x (there p) → high x p })))) prev
    where restore : ∀ {lo hi} → Bounds (a ∷ xs b) lo hi → Bounds (xs (S.extend a b cmp)) lo hi
          restore p rewrite grow-xs a b cmp = p
  sync : ∀ t → Sync (S.partition t) (C.run t)
  sync ε = nil
  sync (t ▻ a) = step _ _ a (sync t)
  close : ∀ s c → Sync s c → Minima (blocks s) (output (C.close c) [])
  close _ _ nil = none
  close (S.active ds b) _ (row (bounds _ (l , low) _) prev) = prev _ _ (pick (forward (xs b) l , (λ x p → low x (backward (xs b) p))) none)
  certified : ∀ t → Minima (Ref.block-list (Ref.Result.partition (Ref.solve (text t)))) (output (C.thinlist t) [])
  certified t = shift (agrees t) (close _ _ (sync t))
    where shift : ∀ {bs cs as} → bs ≡ cs → Minima bs as → Minima cs as
          shift refl m = m
