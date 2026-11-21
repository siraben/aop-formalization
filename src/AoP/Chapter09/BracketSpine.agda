{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketSpine where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image)
private variable A : Set

-- §9.3. To enumerate bracketings while preserving operand order, add
-- a new first operand at a node of the left spine. For b·c there are
-- two places to insert a: a·(b·c) and (a·b)·c. The inverse operation
-- below removes the first tip of any compound expression and remembers
-- exactly where the new first operand belonged.
leaves : Tree A → List A
leaves (tip x) = x ∷ []
leaves (bin l r) = leaves l ++ leaves r

data Place (a : A) : Tree A → Tree A → Set where
  root : ∀ {t} → Place a t (bin (tip a) t)
  descend : ∀ {l l′ r} → Place a l l′ → Place a (bin l r) (bin l′ r)

options : A → Tree A → List (Tree A)
options a (tip b) = bin (tip a) (tip b) ∷ []
options a (bin l r) = bin (tip a) (bin l r) ∷ map (λ l′ → bin l′ r) (options a l)

occurs : ∀ {a : A} {t u} → Place a t u → u ∈ options a t
occurs (root {tip _}) = here
occurs (root {bin _ _}) = here
occurs (descend p) = there (image (λ l → bin l _) (occurs p))

preserves : ∀ {a : A} {t u} → Place a t u → leaves u ≡ a ∷ leaves t
preserves root = refl
preserves (descend {r = r} p) = cong (_++ leaves r) (preserves p)

peel : (l r : Tree A) → Σ _ λ a → Σ _ λ t → Place a t (bin l r)
peel (tip a) r = a , r , root
peel (bin l s) r with peel l s
... | a , t , p = a , bin t r , descend p

-- Calculate the inverse on values (without comparing proofs of Place).
-- At a root insertion the old tree is the right child. At a deeper
-- insertion, peel the left subtree and restore the untouched right one.
remove : (l r : Tree A) → A × Tree A
remove (tip a) r = a , r
remove (bin l s) r with remove l s
... | a , t = a , bin t r

undo : ∀ {a : A} {t l r} → Place a t (bin l r) → remove l r ≡ (a , t)
undo root = refl
undo (descend {l′ = tip _} ())
undo (descend {l′ = bin x y} p) rewrite undo p = refl

-- Even with repeated operand labels, reaching the same compound
-- expression determines both the prepended label and the old tree.
unique-source : ∀ {a b : A} {t u l r} → Place a t (bin l r) → Place b u (bin l r) → (a , t) ≡ (b , u)
unique-source p q = back (undo p) ∙ undo q
  where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
        back refl = refl
