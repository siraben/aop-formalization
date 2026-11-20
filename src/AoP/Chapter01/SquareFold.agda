{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.SquareFold where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturals using (foldn)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

-- Exercise 1.4. To advance from n² to (n+1)², add two strips of
-- length n and the corner cell. Keep the side length alongside the
-- area; the fold uses addition alone. At side three it stores (3,9),
-- so the next step adds four cells and three cells to reach sixteen.
private
  move : ∀ a b → a + suc b ≡ suc (a + b)
  move zero b = refl
  move (suc a) b = cong suc (move a b)

  strip : ∀ a b → a * suc b ≡ a + a * b
  strip zero b = refl
  strip (suc a) b = cong suc (begin
    b + a * suc b ≡⟨ cong (b +_) (strip a b) ⟩
    b + (a + a * b) ≡⟨ swap b a (a * b) ⟩
    a + (b + a * b) ∎)
    where
    swap : ∀ b a c → b + (a + c) ≡ a + (b + c)
    swap zero a c = refl
    swap (suc b) a c = cong suc (swap b a c) ∙ back (move a (b + c))
      where back : ∀ {x y : Nat} → x ≡ y → y ≡ x
            back refl = refl

step : Nat × Nat → Nat × Nat
step (n , area) = suc n , suc n + (n + area)

squares : Nat → Nat × Nat
squares = foldn (0 , 0) step

invariant : ∀ n → squares n ≡ (n , n * n)
invariant zero = refl
invariant (suc n) rewrite invariant n | strip n n = refl

square : Nat → Nat
square n = snd (squares n)

correct : ∀ n → square n ≡ n * n
correct n = cong snd (invariant n)
