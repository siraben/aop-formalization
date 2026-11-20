{-# OPTIONS --safe --without-K #-}
module AoP.SquareMonic where

open import Agda.Builtin.Sigma using (_,_) renaming (fst to fst′)
open import AoP.Categories
open import AoP.ArrowCategory
open import AoP.Cancellation using (module Laws′)

-- Exercise 2.8. Probe a square by arrows out of an identity arrow.
-- A map x into the upper left corner determines the entire probe: its
-- other component must be the composite down the left edge. Therefore
-- monicity of the square forces monicity of its top component.
module Test {o h e} (C : Category o h e) where
  open Category C
  open Arrows C
  open Arrow
  open Square

  probe : ∀ {X} (a : Arrow) (x : Hom X (source a)) → Square (arrow X X identity) a
  probe a x = box x (edge a ∘ x) (symmetric (unitʳ _))

  top-necessary : ∀ {a b} (s : Square a b) → Laws′.Monic Arr s → Laws′.Monic C (top s)
  top-necessary {a} {b} s mon x y eq = fst′ (mon (probe a x) (probe a y) (eq , lower))
    where
    slide : ∀ z → bottom s ∘ (edge a ∘ z) ≈ edge b ∘ (top s ∘ z)
    slide z = transitive (symmetric (assoc _ _ z))
               (transitive (compose-cong (symmetric (commutes s)) reflexive) (assoc _ _ z))
    lower = transitive (slide x) (transitive (compose-cong (reflexive {f = edge b}) eq) (symmetric (slide y)))

  -- With an initial object O, probes from O → X can have any bottom
  -- component. All their top components agree by initiality. Now both
  -- componentwise cancellation tests are necessary as well as sufficient.
  module Initial (O : Obj) (init : ∀ X → Hom O X)
                 (unique : ∀ {X} (u v : Hom O X) → u ≈ v) where
    test : ∀ {X} (a : Arrow) (x : Hom X (target a)) → Square (arrow O X (init X)) a
    test a x = box (init _) x (unique _ _)

    bottom-necessary : ∀ {a b} (s : Square a b) → Laws′.Monic Arr s → Laws′.Monic C (bottom s)
    bottom-necessary {a} s mon x y eq with mon (test a x) (test a y) (unique _ _ , eq)
    ... | _ , q = q
