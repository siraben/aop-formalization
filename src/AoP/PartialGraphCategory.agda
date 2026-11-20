{-# OPTIONS --safe --without-K #-}
module AoP.PartialGraphCategory where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Categories using (Category)
open import Agda.Primitive using (lsuc; lzero)

-- §2.1: Par allows a relation to have no output at an input, but any
-- two outputs there must agree. No decision procedure for definedness
-- is needed. Equality of arrows is mutual inclusion of their graphs.
record Partial (A B : Set) : Set₁ where
  constructor partial
  field edge : B ← A
        single : ∀ {a b c} → edge b a → edge c a → b ≡ c
open Partial
identity : ∀ {A} → Partial A A
identity = partial _≡_ λ { refl refl → refl }
after : ∀ {A B C} → Partial B C → Partial A B → Partial A C
after g f = partial (edge g ∘ edge f) unique
  where unique : ∀ {a b c} → (edge g ∘ edge f) b a → (edge g ∘ edge f) c a → b ≡ c
        unique (i , (p , u)) (j , (q , v)) with single f u v
        ... | refl = single g p q

Par : Category (lsuc lzero) (lsuc lzero) lzero
Category.Obj Par = Set
Category.Hom Par = Partial
Category._≈_ Par f g = (edge f ⊆ edge g) × (edge g ⊆ edge f)
Category.identity Par = identity
Category._∘_ Par = after
Category.reflexive Par = (λ p → p) , (λ p → p)
Category.symmetric Par (u , v) = v , u
Category.transitive Par (u , v) (r , s) = (λ p → r (u p)) , (λ q → v (s q))
Category.compose-cong Par (u , v) (r , s) = (λ { (i , (p , q)) → i , (u p , r q) }) , (λ { (i , (p , q)) → i , (v p , s q) })
Category.unitˡ Par f = (λ { (_ , (refl , p)) → p }) , (λ p → _ , (refl , p))
Category.unitʳ Par f = (λ { (_ , (p , refl)) → p }) , (λ p → _ , (p , refl))
Category.assoc Par t s r = (λ { (i , ((j , (h , g)) , f)) → j , (h , (i , (g , f))) }) , (λ { (j , (h , (i , (g , f)))) → i , ((j , (h , g)) , f) })
