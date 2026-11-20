{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.MonicKernel where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Cancellation using (module Laws′)
open import AoP.Chapter04.Shunting using (Id; graph)

-- Exercise 4.19 in Fun. The kernel relates inputs with a common
-- output. To force two such inputs equal, use them as constant maps
-- from the singleton and cancel m. Conversely the common output of
-- m ∘ f and m ∘ g at each point is exactly a kernel witness.
module Test {A B : Set} (m : A → B) where
  open Laws′ Fun using (Monic)
  M = graph m
  Kernel = M ˘ ∘ M

  reflex : Id ⊆ Kernel
  reflex {a} refl = m a , refl , refl

  diagonal : Monic m → Kernel ⊆ Id
  diagonal cancel {a} {b} (_ , p , q) = cancel {⊤} (λ _ → a) (λ _ → b) (λ _ → p ∙ back q) tt
    where back : ∀ {x y : B} → x ≡ y → y ≡ x
          back refl = refl

  monic : Kernel ⊆ Id → Monic m
  monic collapse f g eq x = collapse (m (g x) , eq x , refl)
