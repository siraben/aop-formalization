{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ImageGraphFunctor where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter04.Power using (_≐_)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 5.1. In ordinary sets send each relation to the *graph*
-- of its existential image. Enlarging the relation can change the
-- subset returned, invalidating a previously valid graph edge.
-- Parameterize over a small extensional powerset presentation so
-- the resulting arrows have precisely the universe of the source.
module Example (P : Set → Set) (denote : ∀ {A} → P A → A → Set)
  (name : ∀ {A} → (A → Set) → P A)
  (reads : ∀ {A} (X : A → Set) → denote (name X) ≐ X)
  (unique : ∀ {A} (x y : P A) → denote x ≐ denote y → x ≡ y) where
  image : ∀ {A B} → B ← A → P A → B → Set
  image R x b = Σ _ λ a → R b a × denote x a
  Graph : ∀ {A B} → B ← A → P B ← P A
  Graph R y x = denote y ≐ image R x
  unit-out : ∀ {A} → Graph (Id {A}) ⊆ Id
  unit-out {b = y} {a = x} (f , g) = unique y x (out , (λ a u → g a (a , refl , u)))
    where out : ∀ a → denote y a → denote x a
          out a u with f a u
          ... | _ , refl , v = v
  unit-in : ∀ {A} → Id ⊆ Graph (Id {A})
  unit-in refl = (λ a u → a , refl , u) , λ { a (_ , refl , u) → u }
  compose : ∀ {A B C} (R : C ← B) (S : B ← A) → Graph R ∘ Graph S ⊆ Graph (R ∘ S)
  compose R S (_ , (f , g) , (h , k)) = (λ c u → let b , r , v = f c u ; a , s , w = h b v in a , (b , r , s) , w) ,
    λ { c (a , (b , r , s) , w) → g c (b , r , k b (a , s , w)) }
  factor : ∀ {A B C} (R : C ← B) (S : B ← A) → Graph (R ∘ S) ⊆ Graph R ∘ Graph S
  factor R S {a = x} (f , g) = name mid , ((λ c u → let a , (b , r , s) , w = f c u in b , r , snd (reads mid) b (a , s , w)) ,
    (λ { c (b , r , v) → let a , s , w = fst (reads mid) b v in g c (a , (b , r , s) , w) })) , reads mid
    where mid = image S x

  data One : Set where star : One
  Empty Full : One ← One
  Empty _ _ = ⊥
  Full _ _ = One
  not-monotone : (Empty ⊆ Full → Graph Empty ⊆ Graph Full) → ⊥
  not-monotone lift = fst (reads (λ (_ : One) → ⊥)) star (snd (lift (λ ()) edge) star (star , star , snd (reads (λ _ → One)) star star))
    where edge : Graph Empty (name (λ _ → ⊥)) (name (λ _ → One))
          edge = (λ a u → absurd (fst (reads (λ _ → ⊥)) a u)) , λ { b (a , () , u) }
            where absurd : ∀ {X : Set} → ⊥ → X
                  absurd ()
