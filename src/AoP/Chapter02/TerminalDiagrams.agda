{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.TerminalDiagrams where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.UniversalObjects using (module Universal)
open import AoP.Chapter02.FunctorCategory using (module Construction)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter02.PreorderCategory using (module Thin)
open import AoP.Common.Prelude using (tt)

-- Exercise 2.22. With the book's orientation an arrow from a to t
-- witnesses R t a. Thus a terminal object is a *least* element.
module Least {A : Set} (R : A → A → Set) (r : ∀ a → R a a)
             (trans : ∀ {a b c} → R a b → R b c → R a c) where
  open Thin R r trans
  open Universal category
  terminal : ∀ t → (∀ a → R t a) → Terminal t
  Terminal.enter (terminal t least) = least
  Terminal.unique (terminal t least) f = tt
  least : ∀ t → Terminal t → ∀ a → R t a
  least t universal = Terminal.enter universal

-- Exercise 2.24. The terminal diagram has value T at every object and
-- identity at every arrow. From any diagram F its unique transformation
-- takes the unique arrow F(X) → T at X. Both paths in each naturality
-- square end at T, so uniqueness at T proves the square commutes.
module Diagrams {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
                {T} (term : Universal.Terminal D T) where
  private module D = Category D
  open Universal.Terminal term
  open Functor using (F₀; F₁)
  constant : Functor C D
  F₀ constant _ = T
  F₁ constant _ = D.identity
  Functor.resp constant _ = D.reflexive
  Functor.identity constant = D.reflexive
  Functor.composition constant _ _ = D.symmetric (D.unitˡ _)

  cones : ∀ F → Natural F constant
  Natural.η (cones F) X = enter (F₀ F X)
  Natural.square (cones F) f = D.transitive (unique _) (D.symmetric (unique _))

  open Universal (Construction.cat C D) using (Terminal)
  terminal-diagram : Terminal constant
  Terminal.enter terminal-diagram = cones
  Terminal.unique terminal-diagram α X = unique (Natural.η α X)
