{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.Trees where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat renaming (Nat to ℕ)
private variable A B : Set

-- §1.4. Binary trees carry data only at tips. Consequently their size
-- algebra counts tips, whereas their depth algebra counts branch levels.
data Tree (A : Set) : Set where
  tip : A → Tree A
  bin : Tree A → Tree A → Tree A

foldt : (A → B) → (B → B → B) → Tree A → B
foldt f g (tip a) = f a
foldt f g (bin l r) = g (foldt f g l) (foldt f g r)

map : (A → B) → Tree A → Tree B
map f = foldt (λ a → tip (f a)) bin

max : ℕ → ℕ → ℕ
max zero y = y
max (suc x) zero = suc x
max (suc x) (suc y) = suc (max x y)

size depth : Tree A → ℕ
size = foldt (λ _ → 1) _+_
depth = foldt (λ _ → 0) λ l r → suc (max l r)

-- A rose tree instead stores one label at each node and any number of
-- children. Naming the forest separately makes both recursion steps visible.
mutual
  data Rose (A : Set) : Set where
    fork : A → Forest A → Rose A
  data Forest (A : Set) : Set where
    null : Forest A
    grow : Rose A → Forest A → Forest A

module RoseFold {A B C : Set} (node : A → C → B) (empty : C) (join : B → C → C) where
  mutual
    tree : Rose A → B
    tree (fork a ts) = node a (forest ts)
    forest : Forest A → C
    forest null = empty
    forest (grow t ts) = join (tree t) (forest ts)

rose-size : Rose A → ℕ
rose-size = RoseFold.tree (λ _ n → suc n) 0 _+_

-- Curried application trees (exercise 1.14). Extend the left spine by one
-- binary application for each argument, preserving its order in the forest.
mutual
  curry : Rose A → Tree A
  curry (fork a ts) = apply (tip a) ts
  apply : Tree A → Forest A → Tree A
  apply t null = t
  apply t (grow u us) = apply (bin t (curry u)) us

-- Peel applications from the outside in. The accumulator holds arguments
-- to the right of the current head; no append is needed.
spine : Tree A → Forest A → Rose A
spine (tip a) ts = fork a ts
spine (bin l r) ts = spine l (grow (spine r null) ts)

uncurry : Tree A → Rose A
uncurry t = spine t null

-- Applying the pending arguments recovers the entire binary expression.
spine-law : (t : Tree A) (ts : Forest A) → curry (spine t ts) ≡ apply t ts
spine-law (tip a) ts = refl
spine-law (bin l r) ts = begin
  curry (spine (bin l r) ts)
    ≡⟨ spine-law l (grow (spine r null) ts) ⟩  -- left induction hypothesis
  apply l (grow (uncurry r) ts)
    ≡⟨⟩  -- consume the next argument
  apply (bin l (curry (uncurry r))) ts
    ≡⟨ cong (λ u → apply (bin l u) ts) (spine-law r null) ⟩
  apply (bin l r) ts ∎

curry-uncurry : (t : Tree A) → curry (uncurry t) ≡ t
curry-uncurry t = spine-law t null

-- Conversely, peeling off the arguments of f(a,b) must recover [a,b],
-- not [b,a]. State the forest lemma with a pending suffix: each argument
-- peeled from a binary application goes immediately before that suffix.
_++ᶠ_ : Forest A → Forest A → Forest A
null ++ᶠ ys = ys
grow x xs ++ᶠ ys = grow x (xs ++ᶠ ys)

unitᶠ : (xs : Forest A) → xs ++ᶠ null ≡ xs
unitᶠ null = refl
unitᶠ (grow x xs) = cong (grow x) (unitᶠ xs)

mutual
  uncurry-curry : (t : Rose A) → uncurry (curry t) ≡ t
  uncurry-curry (fork a xs) = begin
    uncurry (apply (tip a) xs) ≡⟨ peel (tip a) xs null ⟩
    fork a (xs ++ᶠ null)       ≡⟨ cong (fork a) (unitᶠ xs) ⟩
    fork a xs ∎

  peel : (t : Tree A) (xs ys : Forest A) → spine (apply t xs) ys ≡ spine t (xs ++ᶠ ys)
  peel t null ys = refl
  peel t (grow x xs) ys = begin
    spine (apply (bin t (curry x)) xs) ys ≡⟨ peel (bin t (curry x)) xs ys ⟩
    spine t (grow (uncurry (curry x)) (xs ++ᶠ ys))
      ≡⟨ cong (λ u → spine t (grow u (xs ++ᶠ ys))) (uncurry-curry x) ⟩
    spine t (grow x (xs ++ᶠ ys)) ∎
