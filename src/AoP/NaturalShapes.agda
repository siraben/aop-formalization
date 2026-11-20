{-# OPTIONS --safe --without-K #-}
module AoP.NaturalShapes where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Horner using (map)
import AoP.Trees as T
import AoP.Snoc as S

-- Exercise 1.18. Relabelling either component before foo must have the
-- same effect as relabelling every resulting tip afterwards. In our
-- total interpretation the proposed type has an empty-input obstruction.
TreeOp : Set₁
TreeOp = ∀ {A B : Set} → List A × B → T.Tree (A × B)

TreeLaw : TreeOp → Set₁
TreeLaw foo = ∀ {A B C D : Set} (f : A → C) (g : B → D) xs b →
  T.map (λ { (a , v) → f a , g v }) (foo (xs , b)) ≡ foo (map f xs , g b)

no-total-tree-op : TreeOp → ⊥
no-total-tree-op foo = leftmost (foo {⊥} {⊤} ([] , tt))
  where
  leftmost : T.Tree (⊥ × ⊤) → ⊥
  leftmost (T.tip (impossible , _)) = impossible
  leftmost (T.bin l r) = leftmost l

-- Exercise 1.19. A transformation from rose trees to snoc-lists should
-- commute with every relabelling, even when distinct labels become equal.
mutual
  rose-map : ∀ {A B : Set} → (A → B) → T.Rose A → T.Rose B
  rose-map f (T.fork x cs) = T.fork (f x) (forest-map f cs)
  forest-map : ∀ {A B : Set} → (A → B) → T.Forest A → T.Forest B
  forest-map f T.null = T.null
  forest-map f (T.grow t cs) = T.grow (rose-map f t) (forest-map f cs)

snoc-map : ∀ {A B : Set} → (A → B) → S.Snoc A → S.Snoc B
snoc-map f = S.foldl S.ε (λ acc x → acc S.▻ f x)

RoseOp : Set₁
RoseOp = ∀ {A : Set} → T.Rose A → S.Snoc A

RoseLaw : RoseOp → Set₁
RoseLaw foo = ∀ {A B : Set} (f : A → B) t → snoc-map f (foo t) ≡ foo (rose-map f t)

-- A concrete instance selects the root and returns a singleton list.
root : RoseOp
root (T.fork a _) = S.ε S.▻ a

root-law : RoseLaw root
root-law f (T.fork a cs) = refl
