{-# OPTIONS --safe --without-K #-}
module AoP.RelationalPairing where

open import AoP.Prelude
open import AoP.Relations
open import AoP.RelationalProducts using (_⊗_)
private variable A B C D E : Set

-- Pair two choices at the same input. The output is a pair of
-- witnesses, one for each component, with the input shared.
pair : (B ← A) → (C ← A) → B × C ← A
pair R S (b , c) a = R b a × S c a

-- Exercise 5.7. A single intermediate input for four edges supplies
-- an intermediate input for each of the two component paths.
separate : (P : B ← A) (Q : C ← A) (R : D ← A) (S : E ← A) →
           pair P Q ∘ pair R S ˘ ⊆ (P ∘ R ˘) ⊗ (Q ∘ S ˘)
separate P Q R S {b , c} {d , e} (a , (p , q) , r , s) = (a , p , r) , (a , q , s)

-- Exercise 5.8. After the shared input has been paired, independent
-- component steps can be moved into the branches of the pairing.
branches : (R : D ← B) (S : E ← C) (X : B ← A) (Y : C ← A) →
           (R ⊗ S) ∘ pair X Y ⊆ pair (R ∘ X) (S ∘ Y)
branches R S X Y {d , e} ((b , c) , (r , s) , x , y) = (b , r , x) , (c , s , y)

reassemble : (R : D ← B) (S : E ← C) (X : B ← A) (Y : C ← A) →
             pair (R ∘ X) (S ∘ Y) ⊆ (R ⊗ S) ∘ pair X Y
reassemble R S X Y {d , e} ((b , r , x) , (c , s , y)) = (b , c) , (r , s) , x , y
