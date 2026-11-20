{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.CurriedExpression where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees
open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercises 1.13–1.14. A node in this expression may take any number
-- of arguments. The outer call f takes three: g(a,b), h(c), and d.
atom : Char → Rose Char
atom a = fork a null

call : Rose Char
call = fork 'f' (grow g (grow h (grow (atom 'd') null)))
  where
  g = fork 'g' (grow (atom 'a') (grow (atom 'b') null))
  h = fork 'h' (grow (atom 'c') null)

-- Count edges on the longest root-to-leaf path. A child at depth d
-- contributes suc d to its parent's maximum; an empty forest gives 0.
rose-depth : ∀ {A : Set} → Rose A → Nat
rose-depth = RoseFold.tree (λ _ d → d) 0 (λ d rest → max (suc d) rest)

nodes : rose-size call ≡ 7
nodes = refl
levels : rose-depth call ≡ 2
levels = refl

-- Binary application associates to the left: applying f to all three
-- arguments creates three application nodes along the left spine.
infixl 8 _·_
_·_ = bin {Char}
curried : Tree Char
curried = tip 'f' · (tip 'g' · tip 'a' · tip 'b') · (tip 'h' · tip 'c') · tip 'd'

translate : curry call ≡ curried
translate = refl
recover : uncurry curried ≡ call
recover = refl
