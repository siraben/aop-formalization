{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyListCost where

open import AoP.Common.Prelude
open import AoP.Chapter07.Party using (module Planning)
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter01.ConversionCost using (len)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.44, final list extraction. Count the cons cells made by
-- names and namesᶠ. Inviting allocates one cell, omitting allocates
-- none, and siblings share the suffix rather than copying it.
module Law {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Planning rating z add R rid tr mono cmp
  mutual
    cells : ∀ {p t} → Plan p t → Nat
    cells (invite g) = suc (forest-cells g)
    cells (omit g) = forest-cells g
    forest-cells : ∀ {p ts} → Guests p ts → Nat
    forest-cells none = 0
    forest-cells (join plan gs) = cells plan + forest-cells gs

  private
    assoc : ∀ a b c → a + (b + c) ≡ (a + b) + c
    assoc 0 b c = refl
    assoc (suc a) b c = cong suc (assoc a b c)

  mutual
    exact : ∀ {p t} (plan : Plan p t) rest → len (names plan rest) ≡ cells plan + len rest
    exact (invite g) rest = cong suc (forest-exact g rest)
    exact (omit g) rest = forest-exact g rest
    forest-exact : ∀ {p ts} (g : Guests p ts) rest → len (namesᶠ g rest) ≡ forest-cells g + len rest
    forest-exact none rest = refl
    forest-exact (join plan gs) rest = begin
      len (names plan (namesᶠ gs rest)) ≡⟨ exact plan (namesᶠ gs rest) ⟩
      cells plan + len (namesᶠ gs rest) ≡⟨ cong (cells plan +_) (forest-exact gs rest) ⟩
      cells plan + (forest-cells gs + len rest) ≡⟨ assoc (cells plan) (forest-cells gs) (len rest) ⟩
      forest-cells (join plan gs) + len rest ∎
