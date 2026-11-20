{-# OPTIONS --safe --without-K #-}
module AoP.TeXRenderWidth where

open import AoP.Prelude
open import AoP.TeXExternal using (length)
open import AoP.TeXClosestShortest using (numerator)
open import AoP.TeXDistanceScale using (power)
open import AoP.TeXEmitNumerator using (append; places; value)
open import AoP.TeXFraction using (Digit; digit)
open import AoP.TeXCellThreshold using (module At)
open import AoP.StrictUpperQuotient using (choose; cell)
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

private
  restore : ∀ a b → a ≤ b → a + (b - a) ≡ b
  restore 0 b _ = refl
  restore (suc a) (suc b) (s≤ h) = cong suc (restore a b h)
  small : ∀ a b → suc b ≤ a + 10 → b - a ≤ 9
  small 0 b (s≤ h) = h
  small (suc a) 0 h = z≤
  small (suc a) (suc b) (s≤ h) = small a b h
  plus : ∀ x y → x + y ≡ y + x
  plus 0 y = Arithmetic.sym (Arithmetic.unit y)
  plus (suc x) y = cong suc (plus x y) ∙ Arithmetic.sym (Arithmetic.move y x)
  cast : ∀ {x y z} → y ≡ z → x ≤ y → x ≤ z
  cast refl h = h

-- Recurse on the requested width, not on the quotient: an early zero
-- quotient still emits all required leading zeroes.
render : ∀ k n → suc n ≤ power k → Σ (List Digit) (λ ds → (length ds ≡ k) × (numerator ds ≡ n))
render 0 0 _ = [] , (refl , refl)
render 0 (suc n) (s≤ ())
render (suc k) n bound = finish (render k q fits)
  where q = choose 9 n
        c = cell 9 n
        fits = At.upper-back 10 n q c (power k) (cast (Arithmetic.comm 10 (power k)) bound)
        r = n - q * 10
        d = digit r (small (q * 10) n (cast (plus 10 (q * 10)) (snd c)))
        finish : Σ (List Digit) (λ ds → (length ds ≡ k) × (numerator ds ≡ q)) → Σ (List Digit) (λ ds → (length ds ≡ suc k) × (numerator ds ≡ n))
        finish (ds , (l , v)) = append ds d , ((places ds d ∙ cong suc l) , (value ds d ∙ cong (λ i → i * 10 + r) v ∙ restore (q * 10) n (fst c)))
