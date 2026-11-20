{-# OPTIONS --safe --without-K #-}
module AoP.SymmetricTour where

open import AoP.Prelude
open import AoP.Bitonic using (module Tours)
open import AoP.NatOrder using (rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Exercise 8.26. Reversing the tour exchanges the two assignments
-- for every interior city. Under symmetric costs the first interior
-- city can always go outward. For example, the assignments out,in
-- and in,out then represent just one unoriented tour.
module Law {City : Set} (edge : City → City → Nat) (sym : ∀ a b → edge a b ≡ edge b a) where
  open Tours edge
  flip : ∀ {xs} → Route xs → Route xs
  flip close = close
  flip (outward p) = homeward (flip p)
  flip (homeward p) = outward (flip p)

  private
    back : ∀ {a b : Nat} → a ≡ b → b ≡ a
    back refl = refl
    comm : ∀ a b → a + b ≡ b + a
    comm zero zero = refl
    comm zero (suc b) = cong suc (comm zero b)
    comm (suc a) b = cong suc (comm a b) ∙ slide b a
      where slide : ∀ m n → suc (m + n) ≡ m + suc n
            slide zero n = refl
            slide (suc m) n = cong suc (slide m n)

  reverse-cost : ∀ u v e {xs} (p : Route xs) → cost v u e (flip p) ≡ cost u v e p
  reverse-cost u v e close rewrite sym v e | sym e u = comm (edge e v) (edge u e)
  reverse-cost u v e (outward {x} p) rewrite sym x u | reverse-cost x v e p = refl
  reverse-cost u v e (homeward {x} p) rewrite sym v x | reverse-cost u x e p = refl

  canonical : ∀ start interior end → Best start start end interior
  canonical s [] e = close , λ { close → rid _ }
  canonical s (x ∷ xs) e with solve x s e xs
  ... | p , best = outward p , λ where
    (outward q) → sum-mono (rid _) (best q)
    (homeward q) → compare-home q
      where compare-home : (q : Route xs) → cost s s e (outward {x} p) AoP.NatOrder.≤ cost s s e (homeward {x} q)
            compare-home q rewrite sym x s | back (reverse-cost s x e q) = sum-mono (rid _) (best (flip q))
