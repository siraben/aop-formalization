{-# OPTIONS --safe --without-K #-}
module AoP.MuCalculus where

open import Agda.Primitive using (Level; _⊔_)

-- Exercise 6.35. Express equality by the two order directions. Each
-- use of leastness names the candidate prefixpoint and proves its bound.
module Rules {c r : Level} {P : Set c} (_≤_ : P → P → Set r)
             (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z) where
  record Mu (f : P → P) (x : P) : Set (c ⊔ r) where
    field fold : f x ≤ x
          unfold : x ≤ f x
          least : ∀ y → f y ≤ y → x ≤ y
  open Mu

  module Rolling (f g : P → P) (fm : ∀ {a b} → a ≤ b → f a ≤ f b)
                 (gm : ∀ {a b} → a ≤ b → g a ≤ g b)
                 {x y} (fg : Mu (λ a → f (g a)) x) (gf : Mu (λ b → g (f b)) y) where
    -- f y is closed under f ∘ g, and g x under g ∘ f.
    forward : x ≤ f y
    forward = least fg (f y) (fm (fold gf))
    backward : f y ≤ x
    backward = trans (fm (least gf (g x) (gm (fold fg)))) (fold fg)

  module Diagonal (h : P → P → P) (hm : ∀ a {b c} → b ≤ c → h a b ≤ h a c)
                  (inner : P → P) (rows : ∀ a → Mu (h a) (inner a))
                  {n d} (nested : Mu inner n) (diag : Mu (λ a → h a a) d) where
    forward : n ≤ d
    forward = least nested d (least (rows d) d (fold diag))
    backward : d ≤ n
    backward = least diag n (trans (hm n (unfold nested))
                              (trans (fold (rows n)) (fold nested)))

  -- Substitution: roll f out of the outer binder. What remains is
  -- a nested fixed point with row at a given by h (f a); diagonalize
  -- those rows before applying f again.
  module Substitution (f inner : P → P) (h : P → P → P)
         (fm : ∀ {a b} → a ≤ b → f a ≤ f b)
         (im : ∀ {a b} → a ≤ b → inner a ≤ inner b)
         (hm : ∀ a {b c} → b ≤ c → h a b ≤ h a c)
         (rows : ∀ a → Mu (h a) (inner a))
         {x n d} (outer : Mu (λ a → f (inner a)) x)
         (rolled : Mu (λ a → inner (f a)) n)
         (diagonal : Mu (λ a → h (f a) a) d) where
    private
      module R = Rolling f inner fm im outer rolled
      module D = Diagonal (λ a → h (f a)) (λ a → hm (f a))
                          (λ a → inner (f a)) (λ a → rows (f a)) rolled diagonal
    forward : x ≤ f d
    forward = trans R.forward (fm D.forward)
    backward : f d ≤ x
    backward = trans (fm D.backward) R.backward
