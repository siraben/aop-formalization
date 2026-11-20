{-# OPTIONS --safe --without-K #-}
module AoP.SingletonImage where

open import AoP.Prelude
open import AoP.UniversalImage using (Some; All; miss)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (true)
private variable A B : Set

-- Exercise 2.15. Mapping a singleton by ordinary direct image gives
-- the singleton of its mapped element. Prove the two sets have exactly
-- the same members, rather than assuming equality of predicate functions.
singleton : A → A → Set
singleton a x = a ≡ x

out : ∀ (f : A → B) a b → Some f (singleton a) b → singleton (f a) b
out f a b (_ , hit , refl) = hit

into : ∀ (f : A → B) a b → singleton (f a) b → Some f (singleton a) b
into f a b hit = a , hit , refl

-- Try the same square for the universal image of exercise 2.13. The
-- function miss sends the sole input to false. Its universal image
-- includes true because true has no preimage; the mapped singleton
-- contains only false. Thus one inclusion of the square already fails.
extra : All miss (singleton tt) true
extra a ()

fails : (All miss (singleton tt) true → singleton (miss tt) true) → ⊥
fails natural with natural extra
... | ()
