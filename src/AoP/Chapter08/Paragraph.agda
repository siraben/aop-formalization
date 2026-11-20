{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.Paragraph where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

-- §8.5. Break a nonempty sequence of words into nonempty lines without
-- changing their order. Each space costs one column. A layout must fit
-- the margin; the final line, unlike earlier lines, contributes no waste.
-- Here `glue` extends the first line; `new` starts a separate one.
record Nonempty (A : Set) : Set where
  constructor _∷⁺_
  field first : A; rest : List A
open Nonempty

module Layout {Word : Set} (length : Word → Nat) (margin : Nat) where
  Line = Nonempty Word
  Para = Nonempty Line

  new glue : Word → Para → Para
  new w (l ∷⁺ ls) = (w ∷⁺ []) ∷⁺ (l ∷ ls)
  glue w ((u ∷⁺ us) ∷⁺ ls) = (w ∷⁺ (u ∷ us)) ∷⁺ ls

  flatten : List Line → List Word
  flatten [] = []
  flatten ((w ∷⁺ ws) ∷ ls) = w ∷ (ws ++ flatten ls)

  words : Para → List Word
  words (l ∷⁺ ls) = flatten (l ∷ ls)

  new-order : ∀ w p → words (new w p) ≡ w ∷ words p
  new-order w (_ ∷⁺ _) = refl
  glue-order : ∀ w p → words (glue w p) ≡ w ∷ words p
  glue-order w ((_ ∷⁺ _) ∷⁺ _) = refl

  widthFrom : Word → List Word → Nat
  widthFrom w [] = length w
  widthFrom w (v ∷ vs) = suc (length w + widthFrom v vs)

  width : Line → Nat
  width (w ∷⁺ ws) = widthFrom w ws

  fitFrom : Line → List Line → Set
  fitFrom l [] = width l ≤ margin
  fitFrom l (k ∷ ks) = (width l ≤ margin) × fitFrom k ks

  Fits : Para → Set
  Fits (l ∷⁺ ls) = fitFrom l ls

  -- The collection function is a parameter in the book. Here we take
  -- the additive case with a user-supplied penalty for each slack width.
  waste : (Nat → Nat) → Para → Nat
  waste charge (l ∷⁺ ls) = go l ls
    where
    go : Line → List Line → Nat
    go l [] = 0
    go l (k ∷ ks) = charge (margin - width l) + go k ks
