{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.Quad where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool

-- Exercise 3.29. Splitting first on the left bit and then on the
-- right identifies the inputs of any binary Boolean connective with
-- four labelled cases: TT, TF, FT, FF. For conjunction only TT wins.
Four = (⊤ ⊎ ⊤) ⊎ (⊤ ⊎ ⊤)

quad : Bool × Bool → Four
quad (true , true) = inl (inl tt)
quad (true , false) = inl (inr tt)
quad (false , true) = inr (inl tt)
quad (false , false) = inr (inr tt)

bits : Four → Bool × Bool
bits (inl (inl tt)) = true , true
bits (inl (inr tt)) = true , false
bits (inr (inl tt)) = false , true
bits (inr (inr tt)) = false , false

recover : ∀ p → bits (quad p) ≡ p
recover (true , true) = refl
recover (true , false) = refl
recover (false , true) = refl
recover (false , false) = refl

cover : ∀ c → quad (bits c) ≡ c
cover (inl (inl tt)) = refl
cover (inl (inr tt)) = refl
cover (inr (inl tt)) = refl
cover (inr (inr tt)) = refl

conjunction : Four → Bool
conjunction (inl (inl tt)) = true
conjunction (inl (inr tt)) = false
conjunction (inr _) = false

_and_ : Bool → Bool → Bool
true and c = c
false and c = false

and-law : ∀ b c → conjunction (quad (b , c)) ≡ (b and c)
and-law true true = refl
and-law true false = refl
and-law false true = refl
and-law false false = refl
