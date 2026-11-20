{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.LaxMembership where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (ℙ; ℰ)
open import AoP.Chapter05.PowerRelator using (Lift; cover)
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.Relations using (_←_)
private variable A B : Set

-- §5.7. Membership is lax natural from the power relator to identity.
-- Writing out composition avoids putting ℙ B in the universe of B.
-- If b belongs to a related output set, it must have a source in X.
Selected : (B ← A) → ℙ A → B → Set₁
Selected {B = B} R X b = Σ (ℙ B) λ Y → Lift R Y X × Y b

lax : (R : B ← A) (X : ℙ A) → ∀ b → Selected R X b → ℰ R X b
lax R X b (Y , p , y) with Lift.backward p b y
... | a , x , r = a , r , x

-- For a function the inequality becomes an equality: take its whole
-- direct image as the intermediate set. Totality supplies the forward
-- witness even for inputs other than the one producing the chosen b.
image-lift : (f : A → B) (X : ℙ A) → Lift (graph f) (ℰ (graph f) X) X
Lift.backward (image-lift f X) b (a , eq , x) = a , x , eq
Lift.forward (image-lift f X) a x = f a , (a , refl , x) , refl

strict-on-functions : (f : A → B) (X : ℙ A) → ∀ b → ℰ (graph f) X b → Selected (graph f) X b
strict-on-functions f X b member = ℰ (graph f) X , image-lift f X , member
