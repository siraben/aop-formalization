{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ExponentialFunctor where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)

-- Exercise 3.36. Fix B and take L X = X × B. For each target A, the
-- exponential E A represents arrows L X → A by arrows X → E A.
-- Given f : A → D, evaluate an A-valued function, apply f, then curry.
-- The proof uses only the universal property, so L may be any functor
-- with such representing objects.
module Construct {o h e} (C : Category o h e) (L : Functor C C) where
  open Category C
  open Functor L renaming (F₀ to T; F₁ to map)
    using (composition)
  module Represent (E : Obj → Obj) (eval : ∀ A → Hom (T (E A)) A)
    (curry : ∀ {X A} → Hom (T X) A → Hom X (E A))
    (beta : ∀ {X A} (u : Hom (T X) A) → eval A ∘ map (curry u) ≈ u)
    (unique : ∀ {X A} (v : Hom X (E A)) (u : Hom (T X) A) → eval A ∘ map v ≈ u → v ≈ curry u) where
    lift : ∀ {A D} → Hom A D → Hom (E A) (E D)
    lift {A} f = curry (f ∘ eval A)

    -- Move the evaluation through each lifted arrow in turn.
    compose : ∀ {A D G} (g : Hom D G) (f : Hom A D) → lift g ∘ lift f ≈ lift (g ∘ f)
    compose {A} {D} {G} g f = unique _ _ (transitive
      (compose-cong reflexive (composition (lift g) (lift f))) (transitive
      (symmetric (assoc (eval G) _ _)) (transitive
      (compose-cong (beta (g ∘ eval D)) reflexive) (transitive
      (assoc g (eval D) _) (transitive (compose-cong reflexive (beta (f ∘ eval A)))
      (symmetric (assoc g f (eval A))))))))

    exponential : Functor C C
    Functor.F₀ exponential = E
    Functor.F₁ exponential = lift
    Functor.resp exponential {A} {D} {f} eq = unique _ _ (transitive (beta (f ∘ eval A)) (compose-cong eq reflexive))
    Functor.identity exponential {A} = symmetric (unique identity _ (transitive
      (compose-cong reflexive (Functor.identity L)) (transitive (unitʳ (eval A)) (symmetric (unitˡ (eval A))))))
    Functor.composition exponential g f = symmetric (compose g f)
