{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.TaggedThinning where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.RelationalSums using (_⊕_; left; right)
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter08.Thinning using (Pred; Thin; thin)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Power using (_≐_)

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

  R : Pred B → Pred (A ⊎ B)
  R X (inl a) = ⊥
  R X (inr b) = X b

  lift-right : ∀ {X Y} → Thin S X Y → Thin (Q ⊕ S) (R X) (R Y)
  lift-right t = thin (λ { {inl a} () ; {inr b} x → Thin.subset t x }) λ where
    (inl a) ()
    (inr b) y → let a , x , s = Thin.cover t b y in inr a , x , right s

  lower-right : ∀ X Y → Thin (Q ⊕ S) Y (R X) → Thin S (λ b → Y (inr b)) X
  lower-right X Y t = thin (λ x → Thin.subset t x) cover
    where cover : ∀ b → X b → Σ _ λ a → Y (inr a) × S a b
          cover b x with Thin.cover t (inr b) x
          ... | _ , y , right s = _ , y , s

  shape-right : ∀ X Y → Thin (Q ⊕ S) Y (R X) → Y ≐ R (λ b → Y (inr b))
  shape-right X Y t = (λ { (inl a) y → Thin.subset t y ; (inr b) y → y }) ,
                      (λ { (inl a) () ; (inr b) y → y })
