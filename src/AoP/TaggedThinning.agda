{-# OPTIONS --safe --without-K #-}
module AoP.TaggedThinning where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.RelationalSums using (_⊕_; left; right)
open import AoP.Relations using (_←_)
open import AoP.Thinning using (Pred; Thin; thin)
open import AoP.Complement using (⊥)
open import AoP.Power using (_≐_)

-- Exercise 9.5. On a family consisting solely of left-tagged values,
-- thinning cannot introduce a right-tagged candidate. Comparisons of
-- two left-tagged candidates are exactly comparisons under Q.
module Law {A B : Set} (Q : A ← A) (S : B ← B) where
  L : Pred A → Pred (A ⊎ B)
  L X (inl a) = X a
  L X (inr b) = ⊥

  lift : ∀ {X Y} → Thin Q X Y → Thin (Q ⊕ S) (L X) (L Y)
  lift t = thin (λ { {inl a} x → Thin.subset t x ; {inr b} () }) λ where
    (inl b) y → let a , x , q = Thin.cover t b y in inl a , x , left q
    (inr b) ()

  lower : ∀ X Y → Thin (Q ⊕ S) Y (L X) → Thin Q (λ a → Y (inl a)) X
  lower X Y t = thin (λ x → Thin.subset t x) cover
    where cover : ∀ b → X b → Σ _ λ a → Y (inl a) × Q a b
          cover b x with Thin.cover t (inl b) x
          ... | _ , y , left q = _ , y , q

  shape : ∀ X Y → Thin (Q ⊕ S) Y (L X) → Y ≐ L (λ a → Y (inl a))
  shape X Y t = (λ { (inl a) y → y ; (inr b) y → Thin.subset t y }) ,
                (λ { (inl a) y → y ; (inr b) () })
