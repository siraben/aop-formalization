{-# OPTIONS --safe --without-K #-}
module AoP.PowerGraphExtension where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (graph)
open import AoP.Power using (ℙ; ℰ; _≐_)
open import AoP.PowerRelator using (Lift; cover)

-- §5.4. When R is a function graph the two coverage clauses force a
-- unique output subset. The backward clause excludes extra elements;
-- the forward clause includes f a for every a in X. For a general
-- relation the latter clause only asks for *some* related output.
module Graph {A B : Set} (f : A → B) (X : ℙ A) (Y : ℙ B) where
  exact : Lift (graph f) Y X → Y ≐ ℰ (graph f) X
  fst (exact p) b y with Lift.backward p b y
  ... | a , x , eq = a , eq , x
  snd (exact p) b (a , refl , x) with Lift.forward p a x
  ... | _ , y , refl = y

  rebuild : Y ≐ ℰ (graph f) X → Lift (graph f) Y X
  Lift.backward (rebuild eq) b y with fst eq b y
  ... | a , e , x = a , x , e
  Lift.forward (rebuild eq) a x = f a , snd eq (f a) (a , refl , x) , refl

-- Enlarging the relation keeps the same chosen witnesses on both
-- sides, so monotonicity does not require any decision about sets.
monotone : ∀ {A B} {R S : B ← A} {X Y} → R ⊆ S → Lift R Y X → Lift S Y X
Lift.backward (monotone sub p) b y with Lift.backward p b y
... | a , x , r = a , x , sub r
Lift.forward (monotone sub p) a x with Lift.forward p a x
... | b , y , r = b , y , sub r
