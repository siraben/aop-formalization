{-# OPTIONS --safe --without-K #-}
module AoP.SeventeenCutoff where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; rid)
open import AoP.GridTranslation using (Below)
open import AoP.DecimalGridStep using (step)
open import AoP.TeXFraction using (Digit; cshift; intern; halve)
open import AoP.TeXStateBound using (bounded)
open import AoP.SixteenDigitsFail using (take)
open import AoP.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_)

private
  state = ⦅ 0 ∣ cshift ⦆
  pad : ∀ a b → a ≤ a + b
  pad 0 b = z≤
  pad (suc a) b = s≤ (pad a b)
  no : ∀ {n} {X : Set} → suc n ≤ n → X
  no {0} ()
  no {suc n} (s≤ p) = no p
  coarse : ∀ w {x y} → suc x ≤ w → Below w x y
  coarse w small 0 p = z≤
  coarse w small (suc t) p = no (chain small (chain (pad w (t * w)) p))

-- Each layer consumes one input digit, halving the surviving grid
-- width. At depth zero even the entire discarded suffix is too small
-- to reach the first positive threshold. Short inputs stop at nil.
Agreement : Nat → Nat → Set
Agreement n v = ∀ ds → let x = state ds; y = state (take n ds) in Below v x y × Below v y x

end : Agreement 0 131072
end ds = coarse 131072 {state ds} {0} (bounded ds) , coarse 131072 {0} {state ds} (s≤ z≤)

digit : ∀ n v m → m * (2 * v) ≡ 131072 → Agreement n (2 * v) → Agreement (suc n) v
digit n v m eq previous [] = (λ t p → p) , (λ t p → p)
digit n v m eq previous (d ∷ ds) =
  step v m eq d {state ds} {state (take n ds)} (fst (previous ds)) ,
  step v m eq d {state (take n ds)} {state ds} (snd (previous ds))

widths : Agreement 17 1
widths = digit 16 1 65536 refl (digit 15 2 32768 refl (digit 14 4 16384 refl (digit 13 8 8192 refl (digit 12 16 4096 refl (digit 11 32 2048 refl (digit 10 64 1024 refl (digit 9 128 512 refl (digit 8 256 256 refl (digit 7 512 128 refl (digit 6 1024 64 refl (digit 5 2048 32 refl (digit 4 4096 16 refl (digit 3 8192 8 refl (digit 2 16384 4 refl (digit 1 32768 2 refl (digit 0 65536 1 refl (end)))))))))))))))))

private
  unit : ∀ x → x * 1 ≡ x
  unit 0 = refl
  unit (suc x) = cong suc (unit x)
  order : ∀ {x y} → Below 1 x y → x ≤ y
  order {x} h with h x
  ... | f rewrite unit x = f (rid x)
  anti : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
  anti z≤ z≤ = refl
  anti (s≤ p) (s≤ q) = cong suc (anti p q)

cutoff : ∀ ds → intern ds ≡ intern (take 17 ds)
cutoff ds with widths ds
... | xy , yx = cong halve (anti (order xy) (order yx))
