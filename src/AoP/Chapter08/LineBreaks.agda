{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.LineBreaks where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; merge; split; image; preimage)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- §8.5. Before optimizing whitespace, identify the entire search space.
-- For three words there are two gaps and hence four break patterns. At
-- each gap start a fresh line or glue the word to the first existing line.
-- This is a reference enumeration; it deliberately does not prune or test
-- the margin. Even the all-on-one-line layout must occur at this stage.
module Breaks {Word : Set} (length : Word → Nat) (margin : Nat) where
  open Layout length margin

  data Partition : Word → List Word → Para → Set where
    single : ∀ w → Partition w [] ((w ∷⁺ []) ∷⁺ [])
    break-before-tail : ∀ {v vs p} w → Partition v vs p → Partition w (v ∷ vs) (new w p)
    continue-line : ∀ {v vs p} w → Partition v vs p → Partition w (v ∷ vs) (glue w p)

  enumerate : Word → List Word → List Para
  enumerate w [] = ((w ∷⁺ []) ∷⁺ []) ∷ []
  enumerate w (v ∷ vs) = let ps = enumerate v vs in map (new w) ps ++ map (glue w) ps

  complete : ∀ {w ws p} → Partition w ws p → p ∈ enumerate w ws
  complete (single w) = here
  complete (break-before-tail {v} {vs} w q) = merge (map (new w) ps) (map (glue w) ps) (inl (image (new w) (complete q)))
    where ps = enumerate v vs
  complete (continue-line {v} {vs} w q) = merge (map (new w) ps) (map (glue w) ps) (inr (image (glue w) (complete q)))
    where ps = enumerate v vs

  sound : ∀ w ws {p} → p ∈ enumerate w ws → Partition w ws p
  sound w [] here = single w
  sound w [] (there ())
  sound w (v ∷ vs) m with split (map (new w) (enumerate v vs)) (map (glue w) (enumerate v vs)) m
  ... | inl l with preimage (new w) (enumerate v vs) l
  ...   | p , q , refl = break-before-tail w (sound v vs q)
  sound w (v ∷ vs) m | inr r with preimage (glue w) (enumerate v vs) r
  ...   | p , q , refl = continue-line w (sound v vs q)

  preserves-text : ∀ {w ws p} → Partition w ws p → words p ≡ w ∷ ws
  preserves-text (single w) = refl
  preserves-text (break-before-tail {p = p} w q) = begin
    words (new w p) ≡⟨ new-order w p ⟩
    w ∷ words p     ≡⟨ cong (w ∷_) (preserves-text q) ⟩
    _ ∎
  preserves-text (continue-line {p = p} w q) = begin
    words (glue w p) ≡⟨ glue-order w p ⟩
    w ∷ words p      ≡⟨ cong (w ∷_) (preserves-text q) ⟩
    _ ∎
