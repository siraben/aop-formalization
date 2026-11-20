{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.HiddenComparison where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 8.16, adversary argument. On distinct elements drawn from
-- an antichain every member is minimal. For each ordered pair u,v,
-- adding just u ≤ v still gives a preorder. Only that ordered query
-- can distinguish it from equality, but v must now be discarded.
module Hidden {A : Set} (u v : A) (different : u ≡ v → ⊥) where
  Edge : A → A → Set
  Edge a b = (a ≡ b) ⊎ ((a ≡ u) × (b ≡ v))

  trans : ∀ {a b c} → Edge a b → Edge b c → Edge a c
  trans (inl refl) q = q
  trans (inr p) (inl refl) = inr p
  trans (inr (au , bv)) (inr (bu , cv)) = inr (au , cv)

  unchanged : ∀ a b → ((a ≡ u) × (b ≡ v) → ⊥) → Edge a b → a ≡ b
  unchanged a b miss (inl eq) = eq
  unchanged a b miss (inr p) with miss p
  ... | ()

  before : ∀ (X : A → Set) → X v → Min (Test _≡_) v X
  before X xv = xv , λ { _ _ refl → refl }

  after : ∀ (X : A → Set) → X u → Min (Test Edge) v X → ⊥
  after X xu (_ , best) with best u xu (inr (refl , refl))
  ... | inl refl = different refl
  ... | inr (_ , uv) = different uv
