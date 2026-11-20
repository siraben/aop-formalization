{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.GuardedParagraph where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (module Layout; _∷⁺_; Nonempty)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter07.LineWidthClosure using (module Law)
open import AoP.Common.NatOrder using (_≤_; chain)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.23. A new line fits when the word by itself fits;
-- extending the first line checks just the new width. Undoing glue
-- removes one word and space and therefore preserves the fit bound.
module Law′ {W : Set} (size : W → Nat) (margin : Nat) where
  open Layout size margin
  open Breaks size margin hiding (sound; complete)
  data Guarded : W → List W → Para → Set where
    base : ∀ w → size w ≤ margin → Guarded w [] ((w ∷⁺ []) ∷⁺ [])
    fresh : ∀ {v vs p} w → size w ≤ margin → Guarded v vs p → Guarded w (v ∷ vs) (new w p)
    extend : ∀ {v vs l ls} w → widthFrom w (Nonempty.first l ∷ Nonempty.rest l) ≤ margin →
             Guarded v vs (l ∷⁺ ls) → Guarded w (v ∷ vs) (glue w (l ∷⁺ ls))

  change : ∀ l k ls → width k ≤ margin → fitFrom l ls → fitFrom k ls
  change l k [] ok p = ok
  change l k (_ ∷ _) ok p = ok , snd p
  head-ok : ∀ l ls → fitFrom l ls → width l ≤ margin
  head-ok l [] p = p
  head-ok l (_ ∷ _) p = fst p

  sound : ∀ {w ws p} → Guarded w ws p → Partition w ws p × Fits p
  sound (base w ok) = single w , ok
  sound (fresh {p = l ∷⁺ ls} w ok g) with sound g
  ... | p , f = break-before-tail w p , ok , f
  sound (extend {l = v ∷⁺ vs} {ls} w ok g) with sound g
  ... | p , f = continue-line w p , change (v ∷⁺ vs) (w ∷⁺ (v ∷ vs)) ls ok f

  complete : ∀ {w ws p} → Partition w ws p → Fits p → Guarded w ws p
  complete (single w) f = base w f
  complete (break-before-tail {p = l ∷⁺ ls} w p) (ok , f) = fresh w ok (complete p f)
  complete (continue-line {p = (v ∷⁺ vs) ∷⁺ ls} w p) f = extend w ok (complete p shorter)
    where ok = head-ok (w ∷⁺ (v ∷ vs)) ls f
          shorter = change (w ∷⁺ (v ∷ vs)) (v ∷⁺ vs) ls (chain (Law.suffix-width size margin (w ∷ []) v vs) ok) f
