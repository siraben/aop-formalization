{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ImageGraphSetoid where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Power using (_≐_)
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 5.1 with explicit levels. Predicate objects live in Set₁,
-- with extensional equality as identity. No quotient, equality of
-- functions, or small powerset hypothesis is needed for these laws.
Pred : Set → Set₁
Pred A = A → Set
image : ∀ {A B} → B ← A → Pred A → Pred B
image R X b = Σ _ λ a → R b a × X a
Graph : ∀ {A B} → B ← A → Pred B → Pred A → Set
Graph R Y X = Y ≐ image R X
unit : ∀ {A} (Y X : Pred A) → Graph Id Y X → Y ≐ X
unit Y X (f , g) = (λ a y → drop (f a y)) , λ a x → g a (a , refl , x)
  where drop : ∀ {a} → image Id X a → X a
        drop (_ , refl , x) = x
unit′ : ∀ {A} (Y X : Pred A) → Y ≐ X → Graph Id Y X
unit′ Y X (f , g) = (λ a y → a , refl , f a y) , λ { a (_ , refl , x) → g a x }
module Compose {A B C} (R : C ← B) (S : B ← A) (Z : Pred C) (X : Pred A) where
  Middle = Σ (Pred B) λ Y → Graph R Z Y × Graph S Y X
  join : Middle → Graph (R ∘ S) Z X
  join (Y , (f , g) , (h , k)) = (λ c z → let b , r , y = f c z ; a , s , x = h b y in a , (b , r , s) , x) ,
    λ { c (a , (b , r , s) , x) → g c (b , r , k b (a , s , x)) }
  split : Graph (R ∘ S) Z X → Middle
  split (f , g) = image S X , ((λ c z → let a , (b , r , s) , x = f c z in b , r , a , s , x) ,
    (λ { c (b , r , a , s , x) → g c (a , (b , r , s) , x) })) , (λ _ x → x) , (λ _ x → x)

data One : Set where point : One
empty full : One ← One
empty _ _ = ⊥
full _ _ = One
lost : (empty ⊆ full → Graph empty (λ _ → ⊥) (λ _ → One) → Graph full (λ _ → ⊥) (λ _ → One)) → ⊥
lost lift = snd (lift (λ ()) ((λ _ ()) , λ { _ (_ , () , _) })) point (point , point , point)
