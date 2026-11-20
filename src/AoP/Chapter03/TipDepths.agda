{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.TipDepths where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; foldt; map; max; depth)
open import Agda.Builtin.Nat using (Nat; suc)
private variable A : Set

-- §3.2. Label every tip by its distance from the root, then take the
-- largest label. The intermediate tree is a specification: the direct
-- depth fold combines just two numbers at each fork.
tri : (A → A) → Tree A → Tree A
tri f = foldt tip (λ l r → bin (map f l) (map f r))

depths : Tree A → Tree Nat
depths t = tri suc (map (λ _ → 0) t)

largest : Tree Nat → Nat
largest = foldt (λ n → n) max

-- Increasing every tip depth increases the maximum by one. This is
-- the promotion law that removes both maps at the fork.
promote : ∀ t → largest (map suc t) ≡ suc (largest t)
promote (tip _) = refl
promote (bin l r) rewrite promote l | promote r = refl

fused : (t : Tree A) → largest (depths t) ≡ depth t
fused (tip a) = refl
fused (bin l r) = begin
  largest (depths (bin l r)) ≡⟨⟩
  max (largest (map suc (depths l))) (largest (map suc (depths r)))
    ≡⟨ cong (λ n → max n (largest (map suc (depths r)))) (promote (depths l)) ⟩
  max (suc (largest (depths l))) (largest (map suc (depths r)))
    ≡⟨ cong (max (suc (largest (depths l)))) (promote (depths r)) ⟩
  suc (max (largest (depths l)) (largest (depths r)))
    ≡⟨ cong (λ n → suc (max n (largest (depths r)))) (fused l) ⟩
  suc (max (depth l) (largest (depths r))) ≡⟨ cong (λ n → suc (max (depth l) n)) (fused r) ⟩
  depth (bin l r) ∎

example : depths (bin (tip 7) (bin (tip 8) (tip 9))) ≡ bin (tip 1) (bin (tip 2) (tip 2))
example = refl
