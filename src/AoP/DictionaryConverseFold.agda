{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryConverseFold where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Compression using (module Text)
open import AoP.DictionaryConverseStep using (module Step)
open import AoP.DictionaryConverseCases using (module Cases)
open import AoP.DictionaryLastEdge using (module Law)
open import AoP.DictionaryHistory using (module Prefix)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Maybe using (just)

-- Exercise 9.20. Fold a snoc text into its fibre of encodings. At
-- each letter take the relational image of the previous fibre under
-- Extend, retaining all choices. No decidability of letters needed.
module Inverse {A : Set} where
  open Text {A}
  open Step {A}
  open Cases {A} using (complete)
  text : Snoc A → List A
  text ε = []
  text (t ▻ a) = text t ++ (a ∷ [])
  fibre : Snoc A → List Code → Set
  fibre ε qs = qs ≡ []
  fibre (t ▻ a) qs = Σ (List Code) λ ps → fibre t ps × Extend a ps qs
  decode-fold : ∀ t qs → fibre t qs → run [] qs ≡ just (text t)
  decode-fold ε .[] refl = refl
  decode-fold (t ▻ a) qs (ps , generated , edge) = sound edge (decode-fold t ps generated)
  generate : ∀ t qs → run [] qs ≡ just (text t) → fibre t qs
  generate ε [] ok = refl
  generate ε (op ∷ ops) ok with Law.decompose [] op ops ok
  ... | Law.edge ps o xs eq pre step with Law.earlier xs o step
  ... | a , zs , impossible = Prefix.nonempty xs a zs impossible
  generate (t ▻ a) qs ok with complete (text t) a qs ok
  ... | ps , pre , transition = ps , generate t ps pre , transition
