{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.Thinning where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_)

-- Sets are predicates. Min requires both feasibility and optimality (§7.1).
Pred : Set → Set₁
Pred A = A → Set

Min : ∀ {A} → (A ← A) → A → Pred A → Set
Min R a X = X a × (∀ b → X b → R a b)

-- §8.1: thinning can keep multiple incomparable candidates. Each discarded
-- candidate must be dominated by some retained one.
record Thin {A} (Q : A ← A) (X Y : Pred A) : Set where
  constructor thin
  field
    subset : ∀ {a} → X a → Y a
    cover  : ∀ b → Y b → Σ A λ a → X a × Q a b
open Thin

private variable
  A : Set
  Q R : A ← A
  X Y Z : Pred A

thin-id : (∀ a → Q a a) → Thin Q X X
thin-id r = thin (λ x → x) (λ a x → a , x , r a)

thin-compose : (∀ {a b c} → Q a b → Q b c → Q a c) →
               Thin Q X Y → Thin Q Y Z → Thin Q X Z
thin-compose trans p q = thin (λ x → subset q (subset p x)) λ c z →
  let b , y , bc = cover q c z
      a , x , ab = cover p b y
  in a , x , trans ab bc

-- Sound direction of thin-introduction: any minimum found after pruning
-- is still a minimum of the original search space.
min-after-thin : Q ⊆ R → (∀ {a b c} → R a b → R b c → R a c) →
                 Thin Q X Y → ∀ {a} → Min R a X → Min R a Y
min-after-thin sub trans p (x , opt) = subset p x , λ b y →
  let c , xc , cb = cover p b y in trans (opt c xc) (sub cb)

-- Completeness: the nondeterministic thinning may leave the set unchanged.
thin-before-min : (∀ a → Q a a) → ∀ {a} → Min R a Y →
                  Σ (Pred A) λ X → Thin Q X Y × Min R a X
thin-before-min reflQ m = _ , thin-id reflQ , m
