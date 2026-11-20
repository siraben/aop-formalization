{-# OPTIONS --safe --without-K #-}
module AoP.ConverseNonempty where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)

-- Converse function theorem for the nonempty-list signature. A
-- surjective algebra supplies a last decomposition of every state.
-- Compatibility with f determines which input constructor it consumes.
module Law {A S : Set} (f : S → List A) (Tip : A → S → Set)
           (Step : A → S → S → Set)
           (onto : ∀ s → (Σ A λ a → Tip a s) ⊎ (Σ A λ a → Σ S λ r → Step a r s))
           (unit : ∀ {a s} → Tip a s → f s ≡ a ∷ [])
           (cons : ∀ {a s r} → Step a r s → f s ≡ a ∷ f r) where
  data Fold : List A → S → Set where
    single : ∀ {a s} → Tip a s → Fold (a ∷ []) s
    more : ∀ {a xs r s} → Step a r s → Fold xs r → Fold (a ∷ xs) s
  sound : ∀ {xs s} → Fold xs s → f s ≡ xs
  sound (single p) = unit p
  sound (more {a} p q) = cons p ∙ cong (a ∷_) (sound q)

  complete : ∀ xs s → f s ≡ xs → Fold xs s
  complete [] s eq with onto s
  ... | inl (a , p) with rev (unit p) ∙ eq
    where rev : ∀ {u v : List A} → u ≡ v → v ≡ u
          rev refl = refl
  ...   | ()
  complete [] s eq | inr (a , r , p) with rev (cons p) ∙ eq
    where rev : ∀ {u v : List A} → u ≡ v → v ≡ u
          rev refl = refl
  ...   | ()
  complete (b ∷ bs) s eq with onto s
  ... | inl (a , p) with rev (unit p) ∙ eq
    where rev : ∀ {u v : List A} → u ≡ v → v ≡ u
          rev refl = refl
  ...   | refl = single p
  complete (b ∷ bs) s eq | inr (a , r , p) with split (rev (cons p) ∙ eq)
    where rev : ∀ {u v : List A} → u ≡ v → v ≡ u
          rev refl = refl
          split : a ∷ f r ≡ b ∷ bs → (a ≡ b) × (f r ≡ bs)
          split refl = refl , refl
  ...   | refl , tail = more p (complete bs r tail)
