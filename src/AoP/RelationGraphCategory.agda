{-# OPTIONS --safe --without-K #-}
module AoP.RelationGraphCategory where

open import AoP.Prelude
open import AoP.Categories using (Category)
open import AoP.Functors using (Functor)
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.PartialGraphCategory using (Par; Partial; module Partial)
open import Agda.Primitive using (lzero; lsuc)

-- §2.1. In Rel there is no restriction on the number of outputs. The
-- two bracketings of a three-step path retain the same two intermediate
-- points. Only the nesting of the existential witnesses changes.
Rel : Category (lsuc lzero) (lsuc lzero) lzero
Category.Obj Rel = Set
Category.Hom Rel A B = B ← A
Category._≈_ Rel R S = (R ⊆ S) × (S ⊆ R)
Category.identity Rel = _≡_
Category._∘_ Rel = _∘_
Category.reflexive Rel = (λ p → p) , (λ p → p)
Category.symmetric Rel (p , q) = q , p
Category.transitive Rel (p , q) (u , v) = (λ h → u (p h)) , (λ h → q (v h))
Category.compose-cong Rel (p , q) (u , v) = (λ { (b , (s , r)) → b , (p s , u r) }) , (λ { (b , (s , r)) → b , (q s , v r) })
Category.unitˡ Rel R = (λ { (_ , (refl , r)) → r }) , (λ r → _ , (refl , r))
Category.unitʳ Rel R = (λ { (_ , (r , refl)) → r }) , (λ r → _ , (r , refl))
Category.assoc Rel T S R = (λ { (b , ((c , (t , s)) , r)) → c , (t , (b , (s , r))) }) , (λ { (c , (t , (b , (s , r)))) → b , ((c , (t , s)) , r) })

-- Forget the uniqueness proof. Both categories use the same relational
-- composite, so a witness of one composite serves for the other as-is.
forget : Functor Par Rel
Functor.F₀ forget A = A
Functor.F₁ forget = Partial.edge
Functor.resp forget eq = eq
Functor.identity forget = (λ p → p) , (λ p → p)
Functor.composition forget g f = (λ p → p) , (λ p → p)

faithful : ∀ {A B} (f g : Partial A B) → Category._≈_ Rel (Partial.edge f) (Partial.edge g) → Category._≈_ Par f g
faithful f g eq = eq
