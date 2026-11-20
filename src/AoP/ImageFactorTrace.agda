{-# OPTIONS --safe --without-K #-}
module AoP.ImageFactorTrace where

open import AoP.Prelude
open import AoP.Relations
open import AoP.SetoidImageFactor using (module Image)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

-- A table has two distinct rows labelled false and a third labelled true.
-- The image map can use either of the first two as representative. Follow
-- the quotient edge first, then the inclusion edge, to recover the label.
data Row : Set where first second third : Row
label : Row → Bool
label first = false
label second = false
label third = true
open Image label
separate : first ≡ second → ⊥
separate ()
same-entry : EqI first second
same-entry = refl
via-second : (M ∘ C) false first
via-second = second , (refl , refl)
recover-label : false ≡ label first
recover-label = compose {b = false} {a = first} via-second
outside : EqI first third → ⊥
outside ()
