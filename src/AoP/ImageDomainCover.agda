{-# OPTIONS --safe --without-K #-}
module AoP.ImageDomainCover where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Power using (ℙ; ℰ; _≐_)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.DomainPullback using (dom)

-- Exercise 5.16. When the domain test covers an input set X and an
-- intermediate set Z, its diagonal edges identify corresponding
-- elements. Every x in X then has an R-output. This supplies the
-- forward half of power coverage; the reverse half is the witness
-- already carried by the existential image of Z.
module Law {A B : Set} (R : B ← A) (X Z : ℙ A) (Y : ℙ B)
           (test : Lift (dom R) Z X) (image : ℰ R Z ≐ Y) where
  result : Lift R Y X
  Lift.forward result a x with Lift.forward test a x
  ... | .a , z , refl , b , r = b , fst image b (a , r , z) , r
  Lift.backward result b y with snd image b y
  ... | a , r , z with Lift.backward test a z
  ...   | .a , x , refl , _ = a , x , r
