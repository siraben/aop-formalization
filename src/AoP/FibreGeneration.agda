{-# OPTIONS --safe --without-K #-}
module AoP.FibreGeneration where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Thinning using (Thin)

-- 8.11. X and Y give retained and exhaustive results at each child
-- input. Lift their coverage to a layer, then use monotonicity of the
-- whole transition S to match the rival's parent result.
module Law {A B : Set} (F : Set → Set) (L : ∀ {U V} → V ← U → F V ← F U)
  (mono : ∀ {U V} (P Q : V ← U) → P ⊆ Q → L P ⊆ L Q)
  (split : ∀ {U V W} (P : W ← V) (Q : V ← U) → L (P ∘ Q) ⊆ L P ∘ L Q)
  (Q : B ← B) (S : B ← F B) (simulate : S ∘ L (Q ˘) ⊆ Q ˘ ∘ S)
  (X Y : B ← A) (children : ∀ a → Thin Q (λ b → X b a) (λ b → Y b a)) where
  covered : Y ⊆ Q ˘ ∘ X
  covered {a = a} y with Thin.cover (children a) _ y
  ... | v , x , better = v , better , x
  included : X ⊆ Y
  included {a = a} = Thin.subset (children a)
  generate : ∀ t → Thin Q (λ b → (S ∘ L X) b t) (λ b → (S ∘ L Y) b t)
  Thin.subset (generate t) (u , s , x) = u , s , mono X Y included x
  Thin.cover (generate t) b (u , s , y) with split (Q ˘) X (mono Y (Q ˘ ∘ X) covered y)
  ... | v , le , x with simulate (u , s , le)
  ... | z , better , evaluated = z , (v , evaluated , x) , better
