{-# OPTIONS --safe --without-K #-}
module AoP.MinimumUnionGuard where

open import AoP.Prelude
open import AoP.Power using (ℙ)
open import AoP.Thinning using (Min)
open import AoP.Relations using (_←_)

-- §7.1 (7.11–12). A selected family of local winners must cover
-- every index. This is stronger than simply taking the union of all
-- available local winners, which silently ignores an empty branch.
module Family {I A : Set} (R : A ← A) (trans : ∀ {a b c} → R a b → R b c → R a c)
  (sets : I → ℙ A) where
  Whole : ℙ A
  Whole a = Σ I (λ i → sets i a)
  Local = λ i a → Min R a (sets i)
  Guard = ∀ i → Σ A (Local i)
  record Selection (Y : ℙ A) : Set where
    field source : ∀ y → Y y → Σ I (λ i → Local i y)
          covers : ∀ i → Σ A (λ y → Y y × Local i y)
  TwoStage : A → Set₁
  TwoStage a = Σ (ℙ A) λ Y → Selection Y × Min R a Y
  forward : ∀ {a} → TwoStage a → Min R a Whole × Guard
  forward (Y , sel , member , best) with Selection.source sel _ member
  ... | i , xi , _ = ((i , xi) , bound) , (λ j → let y , _ , win = Selection.covers sel j in y , win)
    where bound : ∀ b → Whole b → R _ b
          bound b (j , xb) with Selection.covers sel j
          ... | y , chosen , _ , local-best = trans (best y chosen) (local-best b xb)

  -- Use *all* local minima. The global minimum belongs to the branch
  -- witnessing its feasibility and hence is itself one of those minima.
  backward : ∀ {a} → Min R a Whole × Guard → TwoStage a
  backward {a} (((i , xi) , best) , guard) = Y , sel , (i , xi , (λ b xb → best b (i , xb))) , wins
    where
      Y = λ y → Σ I (λ j → Local j y)
      sel : Selection Y
      Selection.source sel _ h = h
      Selection.covers sel j with guard j
      ... | y , win = y , (j , win) , win
      wins : ∀ b → Y b → R a b
      wins b (j , xb , _) = best b (j , xb)

-- The union of an empty branch and a singleton still has a minimum.
-- No choice of ties can repair the missing witness for the empty branch.
module EmptyBranch where
  open import Agda.Builtin.Bool using (Bool; true; false)
  open import AoP.Complement using (⊥)
  branch : Bool → ℙ ⊤
  branch false _ = ⊥
  branch true _ = ⊤
  module Test = Family {A = ⊤} (λ _ _ → ⊤) (λ _ _ → tt) branch
  global : Min (λ _ _ → ⊤) tt Test.Whole
  global = (true , tt) , (λ _ _ → tt)
  impossible : Test.TwoStage tt → ⊥
  impossible p = fst (snd (snd (Test.forward p) false))
