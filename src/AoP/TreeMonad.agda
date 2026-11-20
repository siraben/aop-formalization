{-# OPTIONS --safe --without-K #-}
module AoP.TreeMonad where

open import AoP.Prelude
open import AoP.Trees using (Tree; bin; tip; map; foldt)
open import AoP.TreeFunctor using (fork-cong)
private variable A B : Set

-- Exercise 2.40, binary-branching case. A leaf holds a variable. In a
-- tree of trees each leaf holds a whole expression: joining substitutes
-- those expressions at the leaves, retaining all surrounding forks.
join : Tree (Tree A) → Tree A
join = foldt (λ t → t) bin

unit-natural : (f : A → B) (a : A) → map f (tip a) ≡ tip (f a)
unit-natural f a = refl

join-natural : (f : A → B) (t : Tree (Tree A)) → map f (join t) ≡ join (map (map f) t)
join-natural f (tip u) = refl
join-natural f (bin l r) = fork-cong (join-natural f l) (join-natural f r)

outer-unit : (t : Tree A) → join (tip t) ≡ t
outer-unit t = refl
inner-unit : (t : Tree A) → join (map tip t) ≡ t
inner-unit (tip a) = refl
inner-unit (bin l r) = fork-cong (inner-unit l) (inner-unit r)

associate : (t : Tree (Tree (Tree A))) → join (join t) ≡ join (map join t)
associate (tip u) = refl
associate (bin l r) = fork-cong (associate l) (associate r)

-- The left subtree is substituted as a unit, rather than rearranged.
example : ∀ (a b c : A) → join (bin (tip (bin (tip a) (tip b))) (tip (tip c))) ≡ bin (bin (tip a) (tip b)) (tip c)
example a b c = refl
