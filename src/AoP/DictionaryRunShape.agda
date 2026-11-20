{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryRunShape where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Compression using (module Text)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionaryStateRuns using (module Runs)
open import AoP.DictionaryConverseFold using (module Inverse)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)

-- A reachable active pointer is determined by the last instruction.
-- In particular, a program ending in a pointer cannot have reached a
-- plain entry via emit. Cancel the final cons-list snoc to recover its
-- exact preceding program, offset and span without equating proofs.
module Shape {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open Text {A}
  open State {A} c p
  open Runs eq? c p
  open Inverse {A} using (text)
  private
    view : Code → List Code → List Code × Code
    view b [] = [] , b
    view b (d ∷ ds) with view d ds
    ... | ps , z = (b ∷ ps) , z
    law : ∀ b ps o → view b (ps ++ (o ∷ [])) ≡ (b ∷ ps , o)
    law b [] o = refl
    law b (d ∷ ds) o rewrite law d ds o = refl
    unpair : Code → List Code → List Code × Code
    unpair b [] = [] , b
    unpair b (d ∷ ds) = view d ds
    end : ∀ b ps o → unpair b (ps ++ (o ∷ [])) ≡ (ps , o)
    end b [] o = refl
    end b (d ∷ ds) o = law d ds o
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
    cancel : ∀ ps qs o z → ps ++ (o ∷ []) ≡ qs ++ (z ∷ []) → (ps , o) ≡ (qs , z)
    cancel ps qs o z e = rev (end o ps o) ∙ cong (unpair o) e ∙ end o qs z

  active-run : ∀ {t j} {u : Entry (text t) j} → Run t (j , u) → ∀ ps i k → program u ≡ ps ++ (ptr i k ∷ []) →
    Σ (List A) λ xs → Σ _ λ pre → Σ _ λ cp → Run t (active xs i k , copying xs i k ps pre cp)
  active-run start-run [] i k ()
  active-run start-run (_ ∷ _) i k ()
  active-run (step path (emit v)) ps i k eq with cancel (program v) ps _ _ eq
  ... | ()
  active-run {u = copying xs j n qs pre cp} r ps i k eq with cancel qs ps (ptr j n) (ptr i k) eq
  ... | refl = xs , pre , cp , r
