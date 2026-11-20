{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.UnzipProjectionLaw where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter04.Shunting using (graph)

-- Exercise 5.10, forward inclusion for concrete Rel. Project an edge
-- through an arbitrary lifting by first composing the two lifted
-- relations, moving the unlifted projection across the edge, then
-- splitting the lifted composite. No traversal of F is required.
module Law (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (map : ∀ {A B} → (A → B) → F A → F B)
  (intro : ∀ {A B} (f : A → B) → graph (map f) ⊆ L (graph f))
  (elim : ∀ {A B} (f : A → B) → L (graph f) ⊆ graph (map f))
  (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {A B C} (P : C ← B) (Q : B ← A) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {A B C} (P : C ← B) (Q : B ← A) → L (P ∘ Q) ⊆ L P ∘ L Q) where
  project : ∀ {A B C D} (f : A → B) (g : C → D) (P : C ← A) (Q : D ← B) →
    (∀ {x y} → P y x → Q (g y) (f x)) → ∀ {u v} → L P v u → L Q (map g v) (map f u)
  project f g P Q square {v = v} edge with split Q (graph f) (mono (graph g ∘ P) (Q ∘ graph f) slide (join (graph g) P (v , intro g refl , edge)))
    where slide : graph g ∘ P ⊆ Q ∘ graph f
          slide (_ , refl , p) = _ , square p , refl
  ... | u′ , q , fe with elim f fe
  ... | refl = q
  tensor : ∀ {A B C D} → C ← A → D ← B → (C × D) ← (A × B)
  tensor P Q y x = P (fst y) (fst x) × Q (snd y) (snd x)
  unzip : ∀ {A B} → F (A × B) → F A × F B
  unzip x = map fst x , map snd x
  forward : ∀ {A B C D} (P : C ← A) (Q : D ← B) → graph unzip ∘ L (tensor P Q) ⊆ tensor (L P) (L Q) ∘ graph unzip
  forward P Q (_ , refl , e) = _ , (project fst fst (tensor P Q) P fst e , project snd snd (tensor P Q) Q snd e) , refl
