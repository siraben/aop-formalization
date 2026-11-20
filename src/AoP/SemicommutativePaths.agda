{-# OPTIONS --safe --without-K #-}
module AoP.SemicommutativePaths where

open import AoP.Prelude
open import AoP.Relations

-- Exercise 4.2. Fix the two side vertices x,y. Every realization of
-- the solid path must admit a realization of the dashed path with the
-- same endpoints. A backwards traversal contributes a converse.
module First {X Y A B C : Set} (S : A ← X) (R : A ← B) (V : Y ← B)
             (T : X ← C) (U : Y ← C) where
  Fill = ∀ x y a b → S a x → R a b → V y b → Σ C (λ c → T x c × U y c)
  Inequation = (V ∘ R ˘ ∘ S) ⊆ (U ∘ T ˘)
  translate : Fill → Inequation
  translate f {y} {x} (b , (v , (a , (r , s)))) with f x y a b s r v
  ... | c , (t , u) = c , (u , t)
  read-back : Inequation → Fill
  read-back h x y a b s r v with h (b , (v , (a , (r , s))))
  ... | c , (u , t) = c , (t , u)

module Second {X Y A B C : Set} (R : X ← A) (S : Y ← A)
              (T : X ← B) (U : C ← B) (V : C ← Y) where
  Fill = ∀ x y a → R x a → S y a → Σ B (λ b → Σ C (λ c → T x b × (U c b × V c y)))
  Inequation = (S ∘ R ˘) ⊆ (V ˘ ∘ U ∘ T ˘)
  translate : Fill → Inequation
  translate f {y} {x} (a , (s , r)) with f x y a r s
  ... | b , (c , (t , (u , v))) = c , (v , (b , (u , t)))
  read-back : Inequation → Fill
  read-back h x y a r s with h (a , (s , r))
  ... | c , (v , (b , (u , t))) = b , (c , (t , (u , v)))
