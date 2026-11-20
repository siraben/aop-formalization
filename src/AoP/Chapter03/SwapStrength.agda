{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.SwapStrength where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Categories using (Fun; Category)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.ProductCategory using (module Product)

-- Exercise 3.40, counterexample. In Fun × Fun the two coordinates of
-- an arrow are independent. Swapping them gives an ordinary functor.
-- But an internal map component would have to transform a function in
-- the first coordinate into a function in the *other* coordinate,
-- without receiving that coordinate's input function.
C = Product.prod Fun Fun
open Category C using (Obj; Hom)
swap : Functor C C
Functor.F₀ swap (a , b) = b , a
Functor.F₁ swap (f , g) = g , f
Functor.resp swap (p , q) = q , p
Functor.identity swap = (λ _ → refl) , (λ _ → refl)
Functor.composition swap _ _ = (λ _ → refl) , (λ _ → refl)

-- Exponential objects in the product category are formed pointwise.
space : Obj → Obj → Obj
space (a , b) (x , y) = (a → x) , (b → y)
S = Functor.F₀ swap

-- Take source (1,1) and target (1,0). The first coordinate of the
-- proposed map would send the identity on 1 to a function 1 → 0.
no-component : ((X Y : Obj) → Hom (space X Y) (space (S X) (S Y))) → ⊥
no-component lift = fst (lift (⊤ , ⊤) (⊤ , ⊥)) (λ x → x) tt
