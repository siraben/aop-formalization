{-# OPTIONS --safe --without-K #-}
module AoP.ResidualFactor where

open import AoP.Prelude
open import AoP.Relations

-- Exercise 7.3. To bound every T-result through R ∘ S, factor through
-- a set of intermediate values. The whole R-fibre at c works: each
-- T-result has an S-successor in that fibre. This construction uses
-- the supplied witnesses separately and needs no global choice function.
module Law {A B C D : Set} (R : C ← B) (S : B ← A) (T : A ← D) where
  Direct : C ← D
  Direct c d = ∀ a → T a d → (R ∘ S) c a

  Factored : C → D → Set₁
  Factored c d = Σ (B → Set) λ X → (∀ b → X b → R c b) ×
                  (∀ a → T a d → Σ B λ b → X b × S b a)

  factor : ∀ {c d} → Direct c d → Factored c d
  factor {c} bound = R c , (λ _ x → x) , bound

  compose : ∀ {c d} → Factored c d → Direct c d
  compose (X , lower , reach) a t with reach a t
  ... | b , member , s = b , lower b member , s
