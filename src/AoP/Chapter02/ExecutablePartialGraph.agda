{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ExecutablePartialGraph where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.PartialGraphCategory using (Partial; module Partial)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

-- §2.5: exact criterion for passing a partial graph to the Maybe-based
-- pack operation. A positive domain decision includes a concrete output.
module Represent {A B : Set} (F : Partial A B) where
  open Partial F
  Dom : A → Set
  Dom a = Σ B (λ b → edge b a)
  Test = ∀ a → Dom a ⊎ (Dom a → ⊥)

  record Code : Set where
    field run : A → Maybe B
          sound : ∀ a b → run a ≡ just b → edge b a
          complete : ∀ a b → edge b a → run a ≡ just b

  encode : Test → Code
  Code.run (encode test) a with test a
  ... | inl (b , _) = just b
  ... | inr _ = nothing
  Code.sound (encode test) a b eq with test a
  ... | inl (c , e) with eq
  ...   | refl = e
  Code.sound (encode test) a b () | inr no
  Code.complete (encode test) a b e with test a
  ... | inl (c , h) = cong just (single h e)
  ... | inr no with no (b , e)
  ...   | ()

  -- Conversely, a run decides the domain. Completeness rules out a
  -- hidden graph output whenever execution returns nothing.
  decide : Code → Test
  decide c a with Code.run c a in eq
  ... | just b = inl (b , Code.sound c a b eq)
  ... | nothing = inr (λ { (b , e) → impossible eq (Code.complete c a b e) })
    where impossible : ∀ {v : Maybe B} {b} → v ≡ nothing → v ≡ just b → ⊥
          impossible refl ()
