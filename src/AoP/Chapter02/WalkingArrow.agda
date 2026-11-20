{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.WalkingArrow where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import Agda.Primitive using (lzero)

-- Exercise 2.19. A diagram on two objects and one generating arrow
-- just picks a source, target and arrow. Its maps are pairs of arrows
-- between endpoints satisfying a single commuting-square equation.
data End : Set where
  src dst : End

data Path : End → End → Set where
  ss : Path src src
  dd : Path dst dst
  go : Path src dst

stay : ∀ {x} → Path x x
stay {src} = ss
stay {dst} = dd

then′ : ∀ {x y z} → Path y z → Path x y → Path x z
then′ ss ss = ss
then′ dd r = r
then′ go ss = go

Walking : Category lzero lzero lzero
Walking = record { Obj = End; Hom = Path; _≈_ = λ _ _ → ⊤; identity = stay; _∘_ = then′
                 ; reflexive = tt; symmetric = λ _ → tt; transitive = λ _ _ → tt
                 ; compose-cong = λ _ _ → tt; unitˡ = λ _ → tt; unitʳ = λ _ → tt
                 ; assoc = λ _ _ _ → tt }

module Diagrams {o h e} (C : Category o h e) where
  open Category C
  open Functor using (F₀; F₁)
  diagram : ∀ {A B} → Hom A B → Functor Walking C
  diagram {A} {B} f = record { F₀ = obj; F₁ = act; resp = λ {_} {_} {p} {q} → respect {p = p} {q}; identity = unit; composition = comp }
    where
    obj : End → Obj
    obj src = A
    obj dst = B
    act : ∀ {x y} → Path x y → Hom (obj x) (obj y)
    act ss = identity
    act dd = identity
    act go = f
    respect : ∀ {x y} {p q : Path x y} → ⊤ → act p ≈ act q
    respect {p = ss} {ss} _ = reflexive
    respect {p = dd} {dd} _ = reflexive
    respect {p = go} {go} _ = reflexive
    comp : ∀ {x y z} (q : Path y z) (p : Path x y) → act (then′ q p) ≈ act q ∘ act p
    comp ss ss = symmetric (unitˡ _)
    comp dd p = symmetric (unitˡ _)
    comp go ss = symmetric (unitʳ _)
    unit : ∀ {x} → act (stay {x}) ≈ identity
    unit {src} = reflexive
    unit {dst} = reflexive

  module Maps (F G : Functor Walking C) where
    open Natural using (η; square)
    record Square : Set (Agda.Primitive._⊔_ h e) where
      constructor box
      field at-src : Hom (F₀ F src) (F₀ G src)
            at-dst : Hom (F₀ F dst) (F₀ G dst)
            commutes : F₁ G go ∘ at-src ≈ at-dst ∘ F₁ F go

    read : Natural F G → Square
    read α = box (η α src) (η α dst) (square α go)

    write : Square → Natural F G
    η (write b) src = Square.at-src b
    η (write b) dst = Square.at-dst b
    square (write b) go = Square.commutes b
    square (write b) ss = transitive (compose-cong (Functor.identity G {src}) reflexive)
      (transitive (unitˡ _) (transitive (symmetric (unitʳ _)) (compose-cong reflexive (symmetric (Functor.identity F {src})))))
    square (write b) dd = transitive (compose-cong (Functor.identity G {dst}) reflexive)
      (transitive (unitˡ _) (transitive (symmetric (unitʳ _)) (compose-cong reflexive (symmetric (Functor.identity F {dst})))))

    recover : ∀ α x → η (write (read α)) x ≈ η α x
    recover α src = reflexive
    recover α dst = reflexive
