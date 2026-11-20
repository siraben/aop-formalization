{-# OPTIONS --safe --without-K #-}
module AoP.TreeMemberPath where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)

-- Exercise 6.17. Descend through zero or more children, then read a
-- label at the current node. For tip-labelled trees the path must end
-- at a leaf; for fork-labelled trees it may stop at any internal node.
data Path {T : Set} (child : T ← T) : T ← T where
  stop : ∀ {t} → Path child t t
  via : ∀ {u v t} → child v t → Path child u v → Path child u t

module Tips {A : Set} where
  data T : Set where tip : A → T; bin : T → T → T
  data Child : T ← T where
    left : ∀ {l r} → Child l (bin l r)
    right : ∀ {l r} → Child r (bin l r)
  data Label : A ← T where read : ∀ {a} → Label a (tip a)

  member : A ← T
  member a (tip x) = a ≡ x
  member a (bin l r) = member a l ⊎ member a r

  find : ∀ a t → member a t → (Label ∘ Path Child) a t
  find a (tip .a) refl = _ , read , stop
  find a (bin l r) (inl p) with find a l p
  ... | u , q , path = u , q , via left path
  find a (bin l r) (inr p) with find a r p
  ... | u , q , path = u , q , via right path

  follow : ∀ {a u t} → Path Child u t → Label a u → member a t
  follow stop read = refl
  follow (via left path) q = inl (follow path q)
  follow (via right path) q = inr (follow path q)

module Forks {A : Set} where
  data T : Set where null : T; fork : T → A → T → T
  data Child : T ← T where
    left : ∀ {l x r} → Child l (fork l x r)
    right : ∀ {l x r} → Child r (fork l x r)
  data Label : A ← T where read : ∀ {l x r} → Label x (fork l x r)

  member : A ← T
  member a null = ⊥
  member a (fork l x r) = (a ≡ x) ⊎ (member a l ⊎ member a r)

  find : ∀ a t → member a t → (Label ∘ Path Child) a t
  find a (fork l .a r) (inl refl) = _ , read , stop
  find a (fork l x r) (inr (inl p)) with find a l p
  ... | u , q , path = u , q , via left path
  find a (fork l x r) (inr (inr p)) with find a r p
  ... | u , q , path = u , q , via right path

  follow : ∀ {a u t} → Path Child u t → Label a u → member a t
  follow stop read = inl refl
  follow (via left path) q = inr (inl (follow path q))
  follow (via right path) q = inr (inr (follow path q))
