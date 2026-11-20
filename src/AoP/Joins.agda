{-# OPTIONS --safe --without-K #-}
module AoP.Joins where

open import AoP.Prelude
open import AoP.Relations
private variable A B C I : Set

-- §4.4. A witness for a small indexed join says which branch was taken.
-- A witness for a meet must instead work at *every* index.
⋃ : (I → B ← A) → B ← A
⋃ {I = I} R b a = Σ I λ i → R i b a

⋂ : (I → B ← A) → B ← A
⋂ {I = I} R b a = (i : I) → R i b a

inject : (R : I → B ← A) (i : I) → R i ⊆ ⋃ R
inject R i r = i , r

least : (R : I → B ← A) (T : B ← A) → (∀ i → R i ⊆ T) → ⋃ R ⊆ T
least R T upper (i , r) = upper i r

project : (R : I → B ← A) (i : I) → ⋂ R ⊆ R i
project R i all = all i

greatest : (R : I → B ← A) (T : B ← A) → (∀ i → T ⊆ R i) → T ⊆ ⋂ R
greatest R T lower t i = lower i t

-- Composition distributes over a join on either side. The intermediate
-- value and the branch index are independent existential witnesses, so
-- move the index out to distribute, and back in to collect the branches.
module Right (S : C ← B) (R : I → B ← A) where
  distribute : S ∘ ⋃ R ⊆ ⋃ (λ i → S ∘ R i)
  distribute (b , s , i , r) = i , b , s , r

  collect : ⋃ (λ i → S ∘ R i) ⊆ S ∘ ⋃ R
  collect (i , b , s , r) = b , s , i , r

module Left (S : I → C ← B) (R : B ← A) where
  distribute : ⋃ S ∘ R ⊆ ⋃ (λ i → S i ∘ R)
  distribute (b , (i , s) , r) = i , b , s , r

  collect : ⋃ (λ i → S i ∘ R) ⊆ ⋃ S ∘ R
  collect (i , b , s , r) = b , (i , s) , r
