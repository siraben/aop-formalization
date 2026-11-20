{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryStateMinimum where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.DictionaryRunShape using (module Shape)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionaryStateRuns using (module Runs)
open import AoP.DictionaryStatePrune using (module Pool)
open import AoP.DictionaryStateWinner using (module Winner)
open import AoP.DictionaryConverseStep using (module Step)
open import AoP.DictionaryConverseFold using (module Inverse)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Compression using (module Text)
open import AoP.Naturality using (_++_)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

module Solver {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open Text {A}
  open Runs eq? c p
  open State {A} c p
  open Shape eq? c p
  open Inverse {A}
  open Step {A}
  open Pool eq? c p using (Candidate)
  open Splice {A} c p using (price)
  Witness : Snoc A → List Code → Set
  Witness t qs = Σ (Candidate (text t)) λ w → Run t w × (program (snd w) ≡ qs)
  private
    inj : ∀ {x y : List A} → just x ≡ just y → x ≡ y
    inj refl = refl
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
  replay : ∀ {t a ps qs} → Extend a ps qs → Witness t ps → Witness (t ▻ a) qs
  replay (literal _) ((_ , u) , r , refl) = _ , step r (emit u) , refl
  replay {t} {a} (begin-ptr _ i xs pre found) ((_ , u) , r , refl) with inj (rev pre ∙ valid u)
  ... | refl = _ , step r (start u i one) , refl
    where one : copy i 1 (text t) ≡ just (text t ++ (a ∷ []))
          one rewrite found = refl
  replay {t} {a} (grow-ptr ps i k xs ys pre short long) ((_ , u) , r , eq) with active-run r ps i k eq
  ... | zs , ok , cp , path with inj (rev pre ∙ ok)
  ... | refl with inj (rev short ∙ cp)
  ... | refl = _ , step path (grow long) , refl
  represent : ∀ t qs → fibre t qs → Witness t qs
  represent ε .[] refl = _ , start-run , refl
  represent (t ▻ a) qs (ps , prev , transition) = replay transition (represent t ps prev)
  solve : ∀ t → Σ (List Code) λ ps → (run [] ps ≡ just (text t)) × (∀ qs → run [] qs ≡ just (text t) → price ps ≤ price qs)
  solve t with Winner.At.solve eq? c p t
  ... | ps , valid′ , least = ps , valid′ , bound
    where bound : ∀ qs → run [] qs ≡ just (text t) → price ps ≤ price qs
          bound qs good with represent t qs (generate t qs good)
          ... | w , path , refl = least w path
