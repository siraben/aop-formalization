{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.EntireBridge where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (graph; Id)

-- Exercise 4.24. Two columns h,k of a table determine endpoint pairs.
-- If each pair lies in R ∘ S, relate its row to every intermediate
-- value that witnesses the factorization. Each row then has a value.
-- Conversely an entire bridge supplies one for every row, and the
-- two inclusions turn it into a path between the endpoints.
module Factor {A B C T : Set} (h : T → C) (k : T → A) (R : C ← B) (S : B ← A) where
  H = graph h
  K = graph k
  record Bridge : Set₁ where
    field Q : B ← T
          entire : Id ⊆ Q ˘ ∘ Q
          left : H ∘ Q ˘ ⊆ R
          right : Q ∘ K ˘ ⊆ S
  open Bridge

  construct : H ∘ K ˘ ⊆ R ∘ S → Bridge
  Q (construct incl) b t = R (h t) b × S b (k t)
  entire (construct incl) {t} refl with incl (t , refl , refl)
  ... | b , r , s = b , (r , s) , (r , s)
  left (construct incl) (t , refl , r , s) = r
  right (construct incl) (t , (r , s) , refl) = s

  recover : Bridge → H ∘ K ˘ ⊆ R ∘ S
  recover bridge (t , refl , refl) with entire bridge {t} refl
  ... | b , q , _ = b , left bridge (t , refl , q) , right bridge (t , q , refl)
