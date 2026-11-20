{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditSuffix where

open import AoP.Common.Prelude
open import AoP.Chapter09.EditScript
open import AoP.Chapter09.EditTail using (module Law)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; rid; chain)
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter06.Closure using (module Paths)

-- The unnumbered closure step following the two tail conditions in
-- §9.2. Lift a simulation through a finite sequence of output changes.
module Lift {A B : Set} (T : B ← B) (E : B ← A) (R : A ← A)
            (unit : ∀ x → R x x) (join : ∀ {x y z} → R x y → R y z → R x z)
            (step : T ∘ E ⊆ E ∘ R) where
  follow : ∀ {x y z} → Paths.Star T z y → E y x → (E ∘ R) z x
  follow {x} Paths.stop e = x , e , unit x
  follow (Paths.extend t path) e with follow path e
  ... | mid , prev , r with step (_ , t , prev)
  ...   | out , next , s = out , next , join s r

module Target {A : Set} where
  open Scripts {A} using (Strings; edit)
  data Drop : Strings ← Strings where
    drop : ∀ {x b y} → Drop (x , y) (x , b ∷ y)
  E : Strings ← List (Op A)
  E p es = edit es ≡ p
  R : List (Op A) ← List (Op A)
  R fs es = len fs ≤ len es
  step : Drop ∘ E ⊆ E ∘ R
  step {a = es} (_ , drop {x} {b} {y} , eq) = Law.tail-script es x b y eq
  suffix : Paths.Star Drop ∘ E ⊆ E ∘ R
  suffix (_ , path , eq) = Lift.follow Drop E R (λ _ → rid _) chain step path eq
