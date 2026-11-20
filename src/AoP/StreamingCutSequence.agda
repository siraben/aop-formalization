{-# OPTIONS --safe --without-K #-}
module AoP.StreamingCutSequence where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Naturality using (_++_)
open import AoP.ConnectedStreamInvariant using (module Invariant)
open import AoP.ConnectedPartitionFusion using (module Fusion)
open import AoP.ConnectedReverseCut using (module Restore)
open import AoP.GreedyBoundaryAgreement using (module Agreement)
open import AoP.ConnectedPartitionMinimum using (module Solver)
open import AoP.ConnectedBlock using (module Law)
open import AoP.ConnectedCutLongest using (module Cut)
open import AoP.LongestPrefix using (module Prefix)
open import AoP.LongestConnectedBlock using (module Scan)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Subsequences using (_∈_)
open import AoP.Complement using (⊥)

module Proof {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
  (tr : ∀ {a b c} → Q a b → Q b c → Q a c) (test : ∀ x y → Dec (Q x y ⊎ Q y x)) where
  open Fusion Q rr tr test
  open Invariant Q rr tr test
  open Restore Q
  open Agreement Q
  open Law Q using (Connected)
  open Scan Q rr test using (Cross; cross?)
  open Prefix {A} using (Longest; result)
  snoc : ∀ {B : Set} (xs : List B) a ys → (xs ++ (a ∷ [])) ++ ys ≡ xs ++ (a ∷ ys)
  snoc [] a ys = refl
  snoc (x ∷ xs) a ys = cong (x ∷_) (snoc xs a ys)
  shift : ∀ {xs ys bs} → xs ≡ ys → Cuts ys bs → Cuts xs bs
  shift refl w = w
  sym : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  sym refl = refl
  saved : Snoc Block → List (List A) → List (List A)
  saved ε bs = bs
  saved (ds ▻ b) bs = saved ds (rev (Block.xs b) ∷ bs)
  text : Snoc A → List A
  text ε = []
  text (t ▻ a) = text t ++ (a ∷ [])
  -- The continuation supplies the as-yet undecided boundaries starting
  -- at the active block. Every already closed block can be prepended.
  Inv : List A → State Block → Set
  Inv xs empty = ∀ rest bs → Cuts rest bs → Cuts (xs ++ rest) bs
  Inv xs (active ds b) = ∀ rest bs → Cuts (rev (Block.xs b) ++ rest) bs → Cuts (xs ++ rest) (saved ds bs)
  place : ∀ b a rest bs (g : Longest Connected (b ++ (a ∷ rest))) → Longest.block g ≡ b → Longest.rest g ≡ a ∷ rest → Cuts (a ∷ rest) bs → Cuts (b ++ (a ∷ rest)) (b ∷ bs)
  place [] a rest bs (result .[] .(a ∷ rest) e ok dom) refl refl tail = take (result [] (a ∷ rest) e ok dom) tail
  place (x ∷ xs) a rest bs (result .(x ∷ xs) .(a ∷ rest) e ok dom) refl refl tail = take (result (x ∷ xs) (a ∷ rest) e ok dom) tail
  grow-xs : ∀ a b (cmp : Cross a (Block.xs b)) → Block.xs (extend a b cmp) ≡ a ∷ Block.xs b
  grow-xs a b cmp with cmp (Block.m b) (Block.member b)
  ... | inl _ = refl
  ... | inr _ = refl
  step-inv : ∀ xs s a → Valid s → Inv xs s → Inv (xs ++ (a ∷ [])) (advance (λ x → x) s a)
  step-inv xs empty a ok prev rest bs tail = shift (snoc xs a rest) (prev (a ∷ rest) bs tail)
  step-inv xs (active ds b) a (old , ok) prev with cross? a (Block.xs b)
  ... | inl cmp = λ rest bs tail → shift (snoc xs a rest) (prev (a ∷ rest) bs (shift (sym (cong (λ us → rev us ++ rest) (grow-xs a b cmp) ∙ snoc (rev (Block.xs b)) a rest)) tail))
  ... | inr no = λ rest bs tail → shift (snoc xs a rest) (prev (a ∷ rest) _ (place (rev (Block.xs b)) a rest bs (cut (Block.xs b) a rest ok (barrier a b no)) refl refl tail))
  sequence : ∀ t → Inv (text t) (partition t)
  sequence ε rest bs tail = tail
  sequence (t ▻ a) = step-inv (text t) (partition t) a (reachable t) (sequence t)
  unit : ∀ (xs : List A) → xs ++ [] ≡ xs
  unit [] = refl
  unit (a ∷ xs) = cong (a ∷_) (unit xs)
  final-block : ∀ xs {a} → a ∈ xs → Connected xs → Cuts xs (xs ∷ [])
  final-block [] ()
  final-block bs@(x ∷ xs) at ok = take (result bs [] (unit bs) ok (λ p _ → p)) stop
  blocks : State Block → List (List A)
  blocks empty = []
  blocks (active ds b) = saved ds (rev (Block.xs b) ∷ [])
  close-all : ∀ xs s → Valid s → Inv xs s → Cuts xs (blocks s)
  close-all xs empty _ all = shift (sym (unit xs)) (all [] [] stop)
  close-all xs (active ds b) (_ , ok) all = shift (sym (unit xs)) (all [] _ (shift (unit bs) (final-block bs (forward raw (Block.member b)) good)))
    where raw = Block.xs b
          bs = rev raw
          good : Connected bs
          good x y p q = ok x y (backward raw p) (backward raw q)
  complete : ∀ t → Cuts (text t) (blocks (partition t))
  complete t = close-all (text t) (partition t) (reachable t) (sequence t)
  module Ref = Solver Q rr test
  agrees : ∀ t → blocks (partition t) ≡ Ref.block-list (Ref.Result.partition (Ref.solve (text t)))
  agrees t = Ref.agrees (text t) (complete t)
