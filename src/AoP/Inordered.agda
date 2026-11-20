{-# OPTIONS --safe --without-K #-}
module AoP.Inordered where

open import AoP.Prelude
open import AoP.OrderedMeet using (module Order)
open import AoP.OrderedPivot using (module Join)
open import AoP.Subsequences using (_∈_)
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Shunting using (graph)
open import AoP.Naturality using (_++_)

-- §6.6. A pivot tree here can have *any* labels. The coreflexive
-- inordered filters out the trees that would fail the ordering test
-- after flattening. Moving this test before flattening is one equality
-- in the relational derivation of quicksort.
data Tree (A : Set) : Set where
  null : Tree A
  fork : Tree A → A → Tree A → Tree A

flatten : ∀ {A} → Tree A → List A
flatten null = []
flatten (fork l p r) = flatten l ++ (p ∷ flatten r)

module Check {A : Set} (R : A ← A) (trans : ∀ {x y z} → R x y → R y z → R x z) where
  open Order {A} using (Ordered; nil; ordered)
  open Join R trans
  data Inorder : Tree A → Set where
    leaf : Inorder null
    node : ∀ {l p r} → Inorder l → (∀ {x} → x ∈ flatten l → R x p) →
           (∀ {x} → x ∈ flatten r → R p x) → Inorder r → Inorder (fork l p r)

  read : ∀ {t} → Inorder t → Ordered R (flatten t)
  read leaf = nil
  read (node {l} {p} {r} il before after ir) =
    join (flatten l) p (flatten r) (parts (read il) before after (read ir))

  check : ∀ t → Ordered R (flatten t) → Inorder t
  check null _ = leaf
  check (fork l p r) ok with separate (flatten l) p (flatten r) ok
  ... | parts ls before after rs = node (check l ls) before after (check r rs)

  inordered : Tree A ← Tree A
  inordered u t = (u ≡ t) × Inorder t

  before-flatten : ordered R ∘ graph flatten ⊆ graph flatten ∘ inordered
  before-flatten {a = t} (_ , (refl , ok) , refl) = t , refl , refl , check t ok

  after-flatten : graph flatten ∘ inordered ⊆ ordered R ∘ graph flatten
  after-flatten (_ , refl , refl , ok) = _ , (refl , read ok) , refl
