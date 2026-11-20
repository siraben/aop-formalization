{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.QueryTrace where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; true; false)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)

-- Exercise 8.16. Run an adaptive deterministic query tree with either
-- oracle. Different outputs force a differing answer at a query on
-- the *first* run: until that point the two paths coincide. Thus a
-- hidden-edge change cannot be detected by adapting later queries
-- unless the antichain run itself asks about that edge.
module Tree {Q B : Set} where
  data Program : Set where
    return : B → Program
    ask : Q → (Bool → Program) → Program

  eval : (Q → Bool) → Program → B
  eval f (return b) = b
  eval f (ask q next) = eval f (next (f q))

  trace : (Q → Bool) → Program → List Q
  trace f (return _) = []
  trace f (ask q next) = q ∷ trace f (next (f q))

  module Compare (f g : Q → Bool) where
    Diff = λ q → f q ≡ g q → ⊥
    distinguish : ∀ p → (eval f p ≡ eval g p → ⊥) → Σ Q λ q → (q ∈ trace f p) × Diff q
    distinguish (return b) changed with changed refl
    ... | ()
    distinguish (ask q next) changed with f q in eq | g q in eq′
    ... | true | false = q , here , different eq eq′
      where different : ∀ {a b} → a ≡ true → b ≡ false → a ≡ b → ⊥
            different refl refl ()
    ... | false | true = q , here , different eq eq′
      where different : ∀ {a b} → a ≡ false → b ≡ true → a ≡ b → ⊥
            different refl refl ()
    ... | true | true with distinguish (next true) changed
    ...   | x , m , d = x , there m , d
    distinguish (ask q next) changed | false | false with distinguish (next false) changed
    ...   | x , m , d = x , there m , d
