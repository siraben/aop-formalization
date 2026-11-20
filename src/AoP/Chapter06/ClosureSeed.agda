{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ClosureSeed where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Closure using (module Paths)
open import AoP.Chapter04.Complement using (_⊔_)
open import AoP.Chapter02.Polynomial using (inl; inr)

-- Exercise 6.32. Start with an R edge and extend by any finite
-- number of S edges. Placing the seed on either side gives the two
-- recursion equations. A least prefixpoint that is also closed under
-- one-step unfolding is a least fixed point.
module After {A B : Set} (R : B ← A) (S : B ← B) where
  open Paths S hiding (expose)
  P = Star ∘ R
  roll : R ⊔ (S ∘ P) ⊆ P
  roll (inl r) = _ , stop , r
  roll (inr (_ , edge , y , path , r)) = y , extend edge path , r
  expose : P ⊆ R ⊔ (S ∘ P)
  expose (_ , stop , r) = inl r
  expose (y , extend edge path , r) = inr (_ , edge , y , path , r)
  least : (X : B ← A) → R ⊔ (S ∘ X) ⊆ X → P ⊆ X
  least X k (_ , path , r) = go path r
    where
    go : ∀ {a b c} → Star c b → R b a → X c a
    go stop r = k (inl r)
    go (extend e p) r = k (inr (_ , e , go p r))

module Before {A B : Set} (R : B ← A) (S : A ← A) where
  open Paths S hiding (expose)
  P = R ∘ Star
  roll : R ⊔ (P ∘ S) ⊆ P
  roll (inl r) = _ , r , stop
  roll (inr (_ , (y , r , path) , edge)) = y , r , append (_ , path , singleton edge)

  -- Induct on the path while allowing the seed to be any partial
  -- result already in X. This consumes the path from the seed end.
  least : (X : B ← A) → R ⊔ (X ∘ S) ⊆ X → P ⊆ X
  least X k (_ , r , path) = go path (k (inl r))
    where
    go : ∀ {a b c} → Star b a → X c b → X c a
    go stop x = x
    go (extend e p) x = go p (k (inr (_ , x , e)))

  expose : P ⊆ R ⊔ (P ∘ S)
  expose = least (R ⊔ (P ∘ S)) λ where
    (inl r) → inl r
    (inr (_ , old , e)) → inr (_ , roll old , e)
