{-# OPTIONS --safe --without-K #-}
module AoP.LocaleProductObstruction where

open import AoP.Prelude
open import AoP.LocaleRelations using (Frame)
import AoP.LocaleIdentity as Id
import AoP.LocaleScalarTabulation as Scalar
open import AoP.Complement using (⊥)

-- Exercise 4.25. In a product of two copies of a frame, joins are
-- coordinatewise. A join of copies of (top,top) has identical grades
-- in both coordinates, independently of whether its index is inhabited.
module Square (F : Frame) where
  open Frame F
  product : Frame
  Frame.V product = V × V
  Frame._≤_ product x y = (fst x ≤ fst y) × (snd x ≤ snd y)
  Frame.rid product x = rid _ , rid _
  Frame.chain product (p , q) (r , s) = chain p r , chain q s
  Frame.meet product x y = meet (fst x) (fst y) , meet (snd x) (snd y)
  Frame.left product x y = left _ _ , left _ _
  Frame.right product x y = right _ _ , right _ _
  Frame.pair product (p , q) (r , s) = pair p r , pair q s
  Frame.join product f = join (λ i → fst (f i)) , join (λ i → snd (f i))
  Frame.inject product f i = inject _ i , inject _ i
  Frame.least product f p = least _ (λ i → fst (p i)) , least _ (λ i → snd (p i))
  Frame.distribute product f b = distribute _ (fst b) , distribute _ (snd b)

  module I = Id.Law product
  module S = Scalar.Law product
  open Id.Law F using (top; above)
  -- The constructed top is the join of all pairs. Both projections
  -- include the grade top (witness the pair (top,top)).
  diagonal : ∀ X → fst (S.support X) ≤ snd (S.support X)
  diagonal X = least _ λ x → chain (above _) (chain (inject snd (top , top)) (inject _ x))

  impossible : ∀ low → (top ≤ low → ⊥) → ∀ X →
               Frame._≤_ product (top , low) (S.support X) →
               Frame._≤_ product (S.support X) (top , low) → ⊥
  impossible low distinct X p q = distinct (chain (fst p) (chain (diagonal X) (snd q)))
