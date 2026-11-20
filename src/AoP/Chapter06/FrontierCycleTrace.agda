{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FrontierCycleTrace where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter06.Closure using (module Paths)
open import AoP.Chapter06.ClosureFrontierInvariant using (module Search)
open import AoP.Chapter06.FiniteFrontierClosure using (module Covered)
open import AoP.Chapter06.FiniteFrontierBudget using (Dec)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

-- The ambient vertex set is infinite. Only 0 and 1 communicate;
-- vertex 2 in our cover is deliberately a false candidate.
data Edge : Nat ← Nat where
  up : Edge 1 0
  down : Edge 0 1
edge : ∀ y x → Dec (Edge y x)
edge 0 0 = inr λ ()
edge 0 1 = inl down
edge 0 (suc (suc x)) = inr λ ()
edge 1 0 = inl up
edge 1 (suc x) = inr λ ()
edge (suc (suc y)) x = inr λ ()
seed : ∀ x → Dec (x ≡ 0)
seed 0 = inl refl
seed (suc x) = inr λ ()
verts = 0 ∷ 1 ∷ 2 ∷ []
cover : ∀ x → Search.Reach Edge (_≡ 0) x → x ∈ verts
cover _ (_ , refl , Paths.stop) = here
cover _ (_ , s , Paths.extend up path) = there here
cover _ (_ , s , Paths.extend down path) = here
module Run = Covered verts Edge edge (_≡ 0) seed cover
reachable : Nat → Bool
reachable n with Run.solve n
... | inl _ = true
... | inr _ = false

-- Frontier {0} becomes {1}; expanding 1 rediscovers 0, so the next
-- frontier is empty. Neither the extra token nor an unlisted vertex
-- is reported as reachable.
trace : (reachable 0 ∷ reachable 1 ∷ reachable 2 ∷ reachable 8 ∷ []) ≡ true ∷ true ∷ false ∷ false ∷ []
trace = refl

listing : Run.vertices ≡ 0 ∷ 1 ∷ []
listing = refl
