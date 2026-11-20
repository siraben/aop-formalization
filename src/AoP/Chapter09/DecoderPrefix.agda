{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DecoderPrefix where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DecoderInit using (module Init)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; chain; rid)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

-- §9.4. Iterate the one-letter simulation: every prefix of a decoded
-- text has an encoding costing at most what was spent on the full text.
module Law {A : Set} (c p : Nat) where
  open Text {A}
  open Init {A} c p using (trim; price)
  data Prefix (xs : List A) : List A → Set where
    same : Prefix xs xs
    more : ∀ {ys} a → Prefix xs ys → Prefix xs (ys ++ (a ∷ []))

  private
    init : List A → List A
    init [] = []
    init (a ∷ []) = []
    init (a ∷ b ∷ bs) = a ∷ init (b ∷ bs)
    drop-last : ∀ xs a → init (xs ++ (a ∷ [])) ≡ xs
    drop-last [] a = refl
    drop-last (x ∷ []) a = refl
    drop-last (x ∷ y ∷ ys) a = cong (x ∷_) (drop-last (y ∷ ys) a)
    back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    back refl = refl

  simulate : ∀ {xs ys} → Prefix xs ys → ∀ ops → run [] ops ≡ just ys →
             Σ (List Code) λ qs → (run [] qs ≡ just xs) × (price qs ≤ price ops)
  simulate same ops ok = ops , ok , rid _
  simulate (more {[]} a path) [] ()
  simulate (more {_ ∷ _} a path) [] ()
  simulate (more {ys} a path) (u ∷ us) ok with trim [] u us ok
  ... | qs , zs , b , decoded , split , le with back (drop-last ys a) ∙ cong init split ∙ drop-last zs b
  ... | refl with simulate path qs decoded
  ... | rs , target , cheap = rs , target , chain cheap le
