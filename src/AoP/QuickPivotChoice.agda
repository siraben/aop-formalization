{-# OPTIONS --safe --without-K #-}
module AoP.QuickPivotChoice where

open import AoP.Prelude
open import AoP.QuickFusion using (Cut; cut; output)
open import AoP.PivotFusion using (module Proviso)
open import AoP.PermutationGuard using (module Guard)
open import AoP.PivotPermutation using (module Pivot)
open import AoP.Subsequences using (here; there)
open import AoP.NatOrder using (_≤_; z≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)
open Proviso _≤_ using (Eligible)
open Pivot {Nat} using (Triple)

-- In [0,1] either occurrence can be a pivot. The specification checks
-- the two bounds and the joined permutation; these tests do not force
-- the last pivot chosen by the executable splitter.
xs : List Nat
xs = 0 ∷ 1 ∷ []
first-pivot last-pivot : Triple
first-pivot = [] , 0 , (1 ∷ [])
last-pivot = (0 ∷ []) , 1 , []
allowed : Eligible first-pivot xs
allowed = ((λ ()) , (λ { here → z≤ ; (there ()) })) , Guard.identity xs
chosen : output 0 (1 ∷ []) ≡ last-pivot
chosen = refl
distinct : Cut first-pivot xs → ⊥
distinct ()

-- The distinction persists in the fusion calculation itself. Permuting
-- either flattened child cannot change the pivot of the checked fork.
open import AoP.Inordered using (fork; null)
open import AoP.PivotCalculation using (module Steps)
open import AoP.Relations using (_∘_; _˘)
module Calc = Steps _≤_
open Proviso _≤_ using (Branch)
open Pivot {Nat} using (Fperm)
branch : Branch
branch = null , 0 , fork null 1 null
permitted : Calc.start xs branch
permitted = xs , Guard.identity xs , fork null 0 (fork null 1 null) , refl , branch , refl , refl , fst allowed

private
  actual : ∀ {t} → Cut t xs → t ≡ last-pivot
  actual (cut .0 .(1 ∷ [])) = refl
  impossible : 1 ≡ 0 → ⊥
  impossible ()

unreachable : (Cut ˘ ∘ (Fperm ∘ Calc.Trees)) xs branch → ⊥
unreachable (t , c , _ , (_ , pivot-eq , _) , refl) with actual c
... | refl = impossible pivot-eq
