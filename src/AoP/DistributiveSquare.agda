{-# OPTIONS --safe --without-K #-}
module AoP.DistributiveSquare where

open import AoP.Prelude
open import AoP.DistributiveHoms using (Bijection; module Law)
open import AoP.InverseNaturality using (module Square)
open Bijection

module Proof {O : Set} (H : O → O → Set) (sum prod exp : O → O → O)
  (cur : ∀ a b t → Bijection (H (prod a b) t) (H a (exp b t)))
  (spl : ∀ a b t → Bijection (H (sum a b) t) (H a t × H b t))
  (a b c s t : O)
  (post : ∀ x → H x s → H x t)
  (epost : ∀ x → H x (exp c s) → H x (exp c t)) where
  module S = Law H sum prod exp cur spl a b c s
  module T = Law H sum prod exp cur spl a b c t
  pair : ∀ {A B C D : Set} → (A → B) → (C → D) → A × C → B × D
  pair f g (x , y) = f x , g y
  module Squares
    (curry-nat : ∀ x f → to (cur x c t) (post (prod x c) f) ≡ epost x (to (cur x c s) f))
    (exp-split : ∀ f → to T.cases (epost (sum a b) f) ≡ pair (epost a) (epost b) (to S.cases f))
    (prod-split : ∀ f → to T.products (post (sum (prod a c) (prod b c)) f) ≡ pair (post (prod a c)) (post (prod b c)) (to S.products f)) where
    private
      undo = λ x → Square.inverse (cur x c s) (cur x c t) (post (prod x c)) (epost x) (curry-nat x)
      merge = Square.inverse S.products T.products (post (sum (prod a c) (prod b c))) (pair (post (prod a c)) (post (prod b c))) prod-split
    -- Move postcomposition through curry, split, both uncurries and merge.
    natural : ∀ f → to T.distribute (post (prod (sum a b) c) f) ≡ post (sum (prod a c) (prod b c)) (to S.distribute f)
    natural f rewrite curry-nat (sum a b) f | exp-split (to S.whole f) with to S.cases (to S.whole f)
    ... | x , y rewrite undo a x | undo b y = merge (from S.l x , from S.r y)
