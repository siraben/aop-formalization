{-# OPTIONS --safe --without-K #-}
module AoP.FiveMoveCylinder where

open import AoP.Prelude
open import AoP.FiniteMinimum using (module Search)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Polynomial using (inl)
open import AoP.NatOrder using (_≤_; chain; sum-mono; rid)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Exercise 7.46. Each suffix can now begin in any of five rows.
-- Enumerate the move labels, even if wraparound makes rows coincide.
data Move : Set where up₂ up₁ stay down₁ down₂ : Move
moves = up₂ ∷ up₁ ∷ stay ∷ down₁ ∷ down₂ ∷ []
listed : ∀ m → m ∈ moves
listed up₂ = here
listed up₁ = there here
listed stay = there (there here)
listed down₁ = there (there (there here))
listed down₂ = there (there (there (there here)))

module Grid (Row : Set) (up down : Row → Row) where
  next : Move → Row → Row
  next up₂ r = up (up r)
  next up₁ r = up r
  next stay r = r
  next down₁ r = down r
  next down₂ r = down (down r)
  Column = Row → Nat
  data Path : List Column → Set where
    exit : Path []
    go : ∀ {d ds} → Move → Path ds → Path (d ∷ ds)
  cost : ∀ {ds} → Column → Row → Path ds → Nat
  cost c r exit = c r
  cost c r (go {d} m p) = c r + cost d (next m r) p
  Best : Column → Row → List Column → Set
  Best c r ds = Σ (Path ds) λ p → (q : Path ds) → cost c r p ≤ cost c r q

  solve : ∀ c r ds → Best c r ds
  solve c r [] = exit , λ { exit → rid _ }
  solve c r (d ∷ ds) = winner
    where suffix = λ m → solve d (next m r) ds
          price = λ m → cost d (next m r) (fst (suffix m))
          module M = Search (λ (_ : Move) → ⊤) (λ _ → inl tt) price
          winner : Best c r (d ∷ ds)
          winner with M.scan moves
          ... | M.none no = M.absurd (no stay (listed stay) tt)
          ... | M.best m _ _ least = go m (fst (suffix m)) , λ where
            (go k q) → sum-mono (rid _) (chain (least k (listed k) tt) (snd (suffix k) q))
