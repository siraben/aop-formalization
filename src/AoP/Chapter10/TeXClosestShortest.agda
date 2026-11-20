{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXClosestShortest where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; intern)
open import AoP.Chapter10.TeXExternal using (length; Shortest; shortest)
open import AoP.Chapter10.TeXShortestSearch using (module W; module Reference)
open import AoP.Chapter10.TeXDigitAlphabet using (complete)
open import AoP.Chapter09.CompressionGrowth using (len)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Common.NatOrder using (_≤_; rid)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

-- For d digits with numerator p, the absolute error has numerator
-- |65536*p - n*10^d| over 65536*10^d. At a fixed length the common
-- denominator cancels. Retain leading zeroes when computing width.
scale : List Digit → Nat
scale [] = 1
scale (_ ∷ ds) = 10 * scale ds
numerator : List Digit → Nat
numerator [] = 0
numerator (d ∷ ds) = Digit.numeral d * scale ds + numerator ds
error : Nat → List Digit → Nat
error n ds = (p - q) + (q - p)
  where p = numerator ds * 65536
        q = n * scale ds

private
  subst : (P : Nat → Set) → ∀ {x y} → x ≡ y → P x → P y
  subst P refl p = p
  eq? : ∀ (x y : Nat) → (x ≡ y) ⊎ (x ≡ y → ⊥)
  eq? 0 0 = inl refl
  eq? 0 (suc y) = inr (λ ())
  eq? (suc x) 0 = inr (λ ())
  eq? (suc x) (suc y) with eq? x y
  ... | inl refl = inl refl
  ... | inr no = inr λ { refl → no refl }
  listed : ∀ ds → ds ∈ W.words (length ds)
  listed ds = W.complete _ (bound ds) (over ds)
    where bound : ∀ es → len es ≤ length es
          bound [] = rid 0
          bound (_ ∷ es) = AoP.Common.NatOrder.s≤ (bound es)
          over : ∀ es → W.Over es
          over [] = W.empty
          over (d ∷ es) = W.extend (complete d) (over es)

record Closest (n : Nat) (ds : List Digit) : Set where
  constructor winner
  field first : Shortest n ds
        second : ∀ es → intern es ≡ n → length es ≡ length ds → error n ds ≤ error n es

module Refine (n : Nat) (base : List Digit) (opt : Shortest n base) where
  P = λ ds → (intern ds ≡ n) × (length ds ≡ length base)
  test : ∀ ds → P ds ⊎ (P ds → ⊥)
  test ds = both (eq? (intern ds) n) (eq? (length ds) (length base))
    where
    both : ∀ {A B : Set} → A ⊎ (A → ⊥) → B ⊎ (B → ⊥) → (A × B) ⊎ (A × B → ⊥)
    both (inl a) (inl b) = inl (a , b)
    both (inr no) _ = inr (λ p → no (fst p))
    both _ (inr no) = inr (λ p → no (snd p))
  open Search P test (error n)
  at-width : ∀ es → length es ≡ length base → es ∈ W.words (length base)
  at-width es eq = subst (λ w → es ∈ W.words w) eq (listed es)
  certify : ∀ xs → (∀ es → length es ≡ length base → es ∈ xs) → Result xs → Σ (List Digit) (Closest n)
  certify xs listed′ (none no) = absurd (no base (listed′ base refl) (Shortest.round-trip opt , refl))
  certify xs listed′ (best ds _ (ok , eq) least) = ds , winner (shortest ok (λ es yes → subst (_≤ length es) (back eq) (Shortest.minimal opt es yes))) (λ es yes w → least es (listed′ es (w ∙ eq)) (yes , (w ∙ eq)))
    where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
          back refl = refl
  choose : Σ (List Digit) (Closest n)
  choose = certify (W.words (length base)) at-width (scan (W.words (length base)))

solve : ∀ n → (Σ (List Digit) (Closest n)) ⊎ (∀ ds → intern ds ≡ n → ⊥)
solve n = finish (Reference.solve n)
  where
  -- Eliminate the certificate without normalizing the concrete 17-digit search.
  finish : Reference.Result′ n → (Σ (List Digit) (Closest n)) ⊎ (∀ ds → intern ds ≡ n → ⊥)
  finish (inl (ds , opt)) = inl (Refine.choose n ds opt)
  finish (inr no) = inr no
