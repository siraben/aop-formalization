{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXShortestSearch where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; intern)
open import AoP.Chapter10.TeXExternal using (length; Shortest; shortest)
open import AoP.Chapter10.TeXDigitAlphabet using (digits; complete)
open import AoP.Chapter09.BoundedWords using (module Words)
open import AoP.Chapter09.CompressionGrowth using (len)
open import AoP.Chapter03.SixteenDigitsFail using (take)
open import AoP.Chapter03.SeventeenCutoff using (cutoff)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; chain)
open import AoP.Chapter05.Subsequences using (_∈_)
open import Agda.Builtin.Nat using (Nat; suc)

-- §10.4 reference specification. Search only through a certified cutoff;
-- truncating *any* rival gives a candidate that is at least as short.
module W = Words digits
private
  eq? : ∀ (x y : Nat) → Dec (x ≡ y)
  eq? 0 0 = inl refl
  eq? 0 (suc y) = inr (λ ())
  eq? (suc x) 0 = inr (λ ())
  eq? (suc x) (suc y) with eq? x y
  ... | inl refl = inl refl
  ... | inr no = inr λ { refl → no refl }
  over : ∀ ds → W.Over ds
  over [] = W.empty
  over (d ∷ ds) = W.extend (complete d) (over ds)
  fits : ∀ k (ds : List Digit) → len (take k ds) ≤ k
  fits 0 ds = z≤
  fits (suc k) [] = z≤
  fits (suc k) (d ∷ ds) = s≤ (fits k ds)
  shorter : ∀ k ds → length (take k ds) ≤ length ds
  shorter 0 ds = z≤
  shorter (suc k) [] = z≤
  shorter (suc k) (d ∷ ds) = s≤ (shorter k ds)
  rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  rev refl = refl

module Bounded (k : Nat) (stable : ∀ ds → intern ds ≡ intern (take k ds)) (n : Nat) where
  Valid = λ ds → intern ds ≡ n
  open Search Valid (λ ds → eq? (intern ds) n) length
  listed : ∀ ds → take k ds ∈ W.words k
  listed ds = W.complete k (fits k ds) (over (take k ds))
  stays : ∀ ds → Valid ds → Valid (take k ds)
  stays ds ok = rev (stable ds) ∙ ok
  Result′ = (Σ (List Digit) λ ds → Shortest n ds) ⊎ (∀ ds → Valid ds → ⊥)
  solve : Result′
  solve with scan (W.words k)
  ... | none no = inr λ ds ok → no (take k ds) (listed ds) (stays ds ok)
  ... | best ds at ok least = inl (ds , shortest ok λ es yes → chain (least (take k es) (listed es) (stays es yes)) (shorter k es))

module Reference = Bounded 17 cutoff
