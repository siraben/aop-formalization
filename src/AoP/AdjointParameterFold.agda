{-# OPTIONS --safe --without-K #-}
module AoP.AdjointParameterFold where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.Whiskering using (module Through)
open import AoP.AlgebraCategory using (module For)
open import AoP.InitialAlgebraFolds using (module From)

-- Exercise 3.41. Fix a parameter. In a cartesian closed category L is
-- product with the parameter and E is the exponential of the result.
-- Only the universal property of evaluation at that result is needed.
module Solve {o h e} (C : Category o h e) (L F G : Functor C C)
  (route : Natural (Through.compose F L) (Through.compose L G)) where
  open Category C
  module L = Functor L
  module F = Functor F
  module G = Functor G
  open For C F
  module At {I} (i : From.U.Initial C F I) {B E : Obj} (h : Hom (G.F₀ B) B)
    (eval : Hom (L.F₀ E) B) (curry : ∀ {X} → Hom (L.F₀ X) B → Hom X E)
    (beta : ∀ {X} (f : Hom (L.F₀ X) B) → eval ∘ L.F₁ (curry f) ≈ f)
    (ext : ∀ {X} (p q : Hom X E) → eval ∘ L.F₁ p ≈ eval ∘ L.F₁ q → p ≈ q) where
    open From.Laws C F i
    open Algebra
    T = carrier I
    η = Natural.η route
    body = (h ∘ G.F₁ eval) ∘ η E
    act = curry body
    target = alg E act
    un : ∀ {X} → Hom X E → Hom (L.F₀ X) B
    un k = eval ∘ L.F₁ k
    result = un (fold target)
    Equation : Hom (L.F₀ T) B → Set e
    Equation f = f ∘ L.F₁ (step I) ≈ (h ∘ G.F₁ f) ∘ η T
    private
      infixr 2 _≈⟨_⟩_
      _≈⟨_⟩_ : ∀ {X Y} (a : Hom X Y) {b c} → a ≈ b → b ≈ c → a ≈ c
      _ ≈⟨ p ⟩ q = transitive p q
    pre : ∀ {X Y} (k : Hom Y E) (m : Hom X Y) → un (k ∘ m) ≈ un k ∘ L.F₁ m
    pre k m = transitive (compose-cong reflexive (L.composition k m)) (symmetric (assoc _ _ _))
    -- Move the recursive carrier map k past the routing operation. This
    -- is the single naturality square needed by both directions.
    slide : ∀ (k : Hom T E) → un (act ∘ F.F₁ k) ≈ (h ∘ G.F₁ (un k)) ∘ η T
    slide k = un (act ∘ F.F₁ k) ≈⟨ pre act _ ⟩
      un act ∘ L.F₁ (F.F₁ k) ≈⟨ compose-cong (beta body) reflexive ⟩
      body ∘ L.F₁ (F.F₁ k) ≈⟨ assoc _ _ _ ⟩
      (h ∘ G.F₁ eval) ∘ (η E ∘ L.F₁ (F.F₁ k)) ≈⟨ compose-cong reflexive (symmetric (Natural.square route k)) ⟩
      (h ∘ G.F₁ eval) ∘ (G.F₁ (L.F₁ k) ∘ η T) ≈⟨ symmetric (assoc _ _ _) ⟩
      ((h ∘ G.F₁ eval) ∘ G.F₁ (L.F₁ k)) ∘ η T ≈⟨ compose-cong (assoc _ _ _) reflexive ⟩
      (h ∘ (G.F₁ eval ∘ G.F₁ (L.F₁ k))) ∘ η T ≈⟨ compose-cong (compose-cong reflexive (symmetric (G.composition eval _))) reflexive ⟩
      reflexive
    respects : ∀ {X} {p q : Hom X E} → p ≈ q → un p ≈ un q
    respects eq = compose-cong reflexive (L.resp eq)
    computes : Equation result
    computes = transitive (symmetric (pre _ _)) (transitive (respects (computation target)) (slide _))
    unique-solution : ∀ f → Equation f → f ≈ result
    unique-solution f eq = transitive (symmetric (beta f)) (respects (unique target (curry f) (ext _ _ square)))
      where square = transitive (pre (curry f) _) (transitive (compose-cong (beta f) reflexive)
              (transitive eq (transitive (compose-cong (compose-cong reflexive (G.resp (symmetric (beta f)))) reflexive) (symmetric (slide (curry f))))))
