{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.LexHeadFold where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter07.LexSubsequence using (module Law)

-- Exercise 7.42. Keep the head when it ties or exceeds the first
-- retained value. On a descending tail, ties can be decided without
-- scanning: the extra equal head merely postpones a drop in value.
module Head {A : Set} (_<_ : A → A → Set)
            (trans : ∀ {a b c} → a < b → b < c → a < c)
            (tri : ∀ a b → (a < b) ⊎ ((a ≡ b) ⊎ (b < a))) where
  open Law _<_ trans tri
  data Desc : List A → Set where
    nil : Desc []
    one : ∀ {a} → Desc (a ∷ [])
    more : ∀ {a b xs} → ((b < a) ⊎ (b ≡ a)) → Desc (b ∷ xs) → Desc (a ∷ b ∷ xs)

  duplicate : ∀ {a xs} → Desc (a ∷ xs) → Lex (a ∷ xs) (a ∷ a ∷ xs)
  duplicate one = common empty
  duplicate (more (inl ba) d) = common (less ba)
  duplicate (more (inr refl) d) = common (duplicate d)

  fast : ∀ xs → Σ _ λ ys → Desc ys × G.Greedy ys xs
  fast [] = [] , nil , G.seed (refl , λ { _ refl → empty })
  fast (a ∷ xs) with fast xs
  ... | [] , nil , g = (a ∷ []) , one , G.step g (keep , λ { _ drop → empty ; _ keep → rid _ })
  ... | (b ∷ bs) , d , g with tri a b
  ...   | inl ab = _ , d , G.step g (drop , λ { _ drop → rid _ ; _ keep → less ab })
  ...   | inr (inr ba) = _ , more (inl ba) d , G.step g (keep , λ { _ drop → less ba ; _ keep → rid _ })
  ...   | inr (inl refl) = _ , more (inr refl) d , G.step g (keep , λ { _ drop → duplicate d ; _ keep → rid _ })
