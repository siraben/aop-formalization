{-# OPTIONS --safe --without-K #-}
module AoP.Schroeder where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Complement using (¬_)

-- Exercise 4.43 in Rel. Given a proposed path a → b → c, a refutation
-- of its endpoint edge in T rules out either step when the other is
-- known. To turn that contradiction back into a positive endpoint edge
-- only membership in T needs to be stable under double negation.
module Rule {A B C : Set} (R : C ← B) (S : B ← A) (T : C ← A) where
  Path = R ∘ S ⊆ T
  First = (¬ T) ∘ S ˘ ⊆ (¬ R)
  Second = R ˘ ∘ (¬ T) ⊆ (¬ S)

  exclude-first : Path → First
  exclude-first path (a , nt , s) r = nt (path (_ , r , s))
  exclude-second : Path → Second
  exclude-second path (c , r , nt) s = nt (path (_ , r , s))

  module Stable (positive : (¬ (¬ T)) ⊆ T) where
    from-first : First → Path
    from-first stop (b , r , s) = positive (λ nt → stop (_ , nt , s) r)
    from-second : Second → Path
    from-second stop (b , r , s) = positive (λ nt → stop (_ , r , nt) s)
