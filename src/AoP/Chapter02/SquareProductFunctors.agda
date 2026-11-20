{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.SquareProductFunctors where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.ProductCategory using (module Product)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter01.Naturality using (cross)
open import Agda.Builtin.Nat using (Nat; suc)

-- §2.2. The product functor may change the two coordinates differently.
-- The square functor specializes its action to two copies of one map.
module P = Product Fun Fun
product : Functor P.prod Fun
Functor.F₀ product (A , B) = A × B
Functor.F₁ product (f , g) = cross f g
Functor.resp product (left , right) (a , b) = both (left a) (right b)
  where both : ∀ {A B : Set} {x y : A} {u v : B} → x ≡ y → u ≡ v → (x , u) ≡ (y , v)
        both refl refl = refl
Functor.identity product (a , b) = refl
Functor.composition product (g , k) (f , h) (a , b) = refl

square : Functor Fun Fun
Functor.F₀ square A = A × A
Functor.F₁ square f = cross f f
Functor.resp square {f = f} {g} p (a , b) = cong (_, f b) (p a) ∙ cong (g a ,_) (p b)
Functor.identity square (a , b) = refl
Functor.composition square g f (a , b) = refl

-- With just one action both coordinates advance. In the bifunctor
-- the right coordinate can instead stay fixed.
advance-both : Functor.F₁ square suc (1 , 4) ≡ (2 , 5)
advance-both = refl
advance-left : Functor.F₁ product {Nat , Nat} {Nat , Nat} (suc , (λ n → n)) (1 , 4) ≡ (2 , 4)
advance-left = refl
