{-# OPTIONS --safe --without-K #-}
module AoP.TeXShortestSearch where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit; intern)
open import AoP.TeXExternal using (length; Shortest; shortest)
open import AoP.TeXDigitAlphabet using (digits; complete)
open import AoP.BoundedWords using (module Words)
open import AoP.CompressionGrowth using (len)
open import AoP.SixteenDigitsFail using (take)
open import AoP.SeventeenCutoff using (cutoff)
open import AoP.FiniteMinimum using (module Search)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain)
open import AoP.Subsequences using (_∈_)
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
