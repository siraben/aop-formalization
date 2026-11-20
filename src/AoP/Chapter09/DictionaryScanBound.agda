{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryScanBound where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionarySearch using (module Encode)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Common.NatOrder using (_≤_; compare; rid; chain)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just; nothing)

-- Local Bellman inequality: each tested one-token extension reaching
-- the requested prefix gives an upper bound on the chosen entry.
module Bound {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Table eq? target c p
  open Text {A}
  open Splice {A} c p using (price)
  open Encode eq? target using (list?; tokens)
  val : ∀ {xs} → Cell xs → Nat
  val u = price (fst u)
  both : ∀ {xs} (u v : Cell xs) → (val (choose u v) ≤ val u) × (val (choose u v) ≤ val v)
  both u v with compare (val u) (val v)
  ... | inl le = rid _ , le
  ... | inr le = le , rid _
  keep : ∀ ys r op best → val (try ys r op best) ≤ val best
  keep ys (xs , ps , ok) op best with reaches? xs op ys
  ... | inr _ = rid _
  ... | inl res = snd (both ((ps ++ (op ∷ [])) , (Splice.resume c p [] ps (op ∷ []) ok ∙ res)) best)
  accept : ∀ ys (r : Row) op best → run (fst r) (op ∷ []) ≡ just ys → val (try ys r op best) ≤ price (fst (snd r) ++ (op ∷ []))
  accept ys (xs , ps , ok) op best success with reaches? xs op ys
  ... | inl res = fst (both ((ps ++ (op ∷ [])) , (Splice.resume c p [] ps (op ∷ []) ok ∙ res)) best)
  ... | inr no with no success
  ...   | ()
  skip : ∀ ys r ops best → val (scan ys r ops best) ≤ val best
  skip ys r [] best = rid _
  skip ys r (op ∷ ops) best = chain (skip ys r ops _) (keep ys r op best)
  token : ∀ ys r ops best op → op ∈ ops → run (fst r) (op ∷ []) ≡ just ys → val (scan ys r ops best) ≤ price (fst (snd r) ++ (op ∷ []))
  token ys r (_ ∷ ops) best op here ok = chain (skip ys r ops _) (accept ys r op best ok)
  token ys r (_ ∷ ops) best op (there m) ok = token ys r ops _ op m ok
  pass : ∀ ys rs best → val (rows ys rs best) ≤ val best
  pass ys [] best = rid _
  pass ys (r ∷ rs) best = chain (pass ys rs _) (skip ys r tokens best)
  edge : ∀ ys rs best r op → r ∈ rs → op ∈ tokens → run (fst r) (op ∷ []) ≡ just ys → val (rows ys rs best) ≤ price (fst (snd r) ++ (op ∷ []))
  edge ys (_ ∷ rs) best r op here m ok = chain (pass ys rs _) (token ys r tokens best op m ok)
  edge ys (_ ∷ rs) best r op (there n) m ok = edge ys rs _ r op n m ok
