{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DepthAccumulator where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; map)
open import AoP.Chapter03.TipDepths using (depths)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
private variable A : Set

-- Exercise 3.48. Label every tip by its distance from the root. At a
-- fork, pass the incremented distance to both children; the triangle
-- specification instead walks the resulting trees to increment labels.
label : Nat → Tree A → Tree Nat
label n (tip _) = tip n
label n (bin l r) = bin (label (suc n) l) (label (suc n) r)

private
  shift : ∀ n (t : Tree A) → map suc (label n t) ≡ label (suc n) t
  shift n (tip _) = refl
  shift n (bin l r) rewrite shift (suc n) l | shift (suc n) r = refl

correct : (t : Tree A) → depths t ≡ label 0 t
correct (tip _) = refl
correct (bin l r) rewrite correct l | correct r | shift 0 l | shift 0 r = refl

-- An arbitrary incoming depth adds that offset to every output tip.
offset : ∀ n (t : Tree A) → map (n +_) (label 0 t) ≡ label n t
offset zero (tip _) = refl
offset zero (bin l r) = identity (label 0 (bin l r))
  where identity : (s : Tree Nat) → map (0 +_) s ≡ s
        identity (tip _) = refl
        identity (bin a b) rewrite identity a | identity b = refl
offset (suc n) t = begin
  map (suc n +_) (label 0 t) ≡⟨ nested (label 0 t) ⟩
  map suc (map (n +_) (label 0 t)) ≡⟨ cong (map suc) (offset n t) ⟩
  map suc (label n t) ≡⟨ shift n t ⟩
  label (suc n) t ∎
  where nested : (s : Tree Nat) → map (suc n +_) s ≡ map suc (map (n +_) s)
        nested (tip _) = refl
        nested (bin a b) rewrite nested a | nested b = refl
