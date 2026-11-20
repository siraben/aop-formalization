{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ConnectedWellBounded where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter06.Inductive using (Acc; acc)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter07.WellBounded using (Bounded; connected)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.26. State the classical case distinctions locally. An
-- inhabited subset has a minimum iff descending searches cannot get
-- stuck at a nonminimum and cannot descend forever (accessibility).
module Law {A : Set} (R : A ← A) where
  Strict : A ← A
  Strict x y = R x y × (R y x → ⊥)
  WF = ∀ x → Acc Strict x
  Connected = ∀ x y → R x y ⊎ R y x
  Dec = λ (P : Set) → P ⊎ (P → ⊥)
  private
    absurd : ∀ {B : Set} → ⊥ → B
    absurd ()
  -- If an inaccessible point exists, take a minimum of the subset of
  -- inaccessible points. All its strict predecessors are accessible.
  necessary : (∀ x → Dec (Acc Strict x)) → Bounded R → Connected × WF
  necessary choose wb = connected wb , all
    where bad = λ x → Acc Strict x → ⊥
          all : WF
          all x with choose x
          ... | inl a = a
          ... | inr no with wb bad x no
          ... | m , impossible , lower = absurd (impossible (acc pred))
            where pred : ∀ y → Strict y m → Acc Strict y
                  pred y (_ , not-back) with choose y
                  ... | inl a = a
                  ... | inr n = absurd (not-back (lower y n))
  -- Search for a member violating the lower-bound test. Connectedness
  -- turns any such witness into a strict predecessor, so recurse there.
  sufficient : Connected → WF → (∀ (X : A → Set) x →
    (Σ A λ y → X y × (R x y → ⊥)) ⊎ (∀ y → X y → R x y)) → Bounded R
  sufficient cmp wf inspect X x xx = descend x (wf x) xx
    where descend : ∀ x → Acc Strict x → X x → Σ A λ m → Min R m X
          descend x (acc smaller) xx with inspect X x
          ... | inr lower = x , xx , lower
          ... | inl (y , yy , no) with cmp y x
          ... | inl le = descend y (smaller y (le , no)) yy
          ... | inr back = absurd (no back)
