{-# OPTIONS --safe --without-K #-}
module AoP.DecidableImageFactor where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- 4.20 in Fun, with decidable inhabited fibres. Store just the value
-- and a token that its fibre test succeeded, not the chosen preimage.
module Factor {A B : Set} (f : A → B) where
  Fibre : B → Set
  Fibre b = Σ A (λ a → f a ≡ b)
  module Build (test : ∀ b → Fibre b ⊎ (Fibre b → ⊥)) where
    Token : ∀ {b} → Fibre b ⊎ (Fibre b → ⊥) → Set
    Token (inl _) = ⊤
    Token (inr _) = ⊥
    I = Σ B (λ b → Token (test b))
    m : I → B
    m = fst
    enter : ∀ b (r : Fibre b ⊎ (Fibre b → ⊥)) → Fibre b → Token r
    enter b (inl _) w = tt
    enter b (inr no) w with no w
    ... | ()
    c : A → I
    c a = f a , enter (f a) (test (f a)) (a , refl)
    factor : ∀ a → m (c a) ≡ f a
    factor a = refl
    unique-token : ∀ b (r : Fibre b ⊎ (Fibre b → ⊥)) (x y : Token r) → x ≡ y
    unique-token b (inl _) tt tt = refl
    unique-token b (inr _) ()
    injective : ∀ {x y} → m x ≡ m y → x ≡ y
    injective {b , x} {.b , y} refl = cong (b ,_) (unique-token b (test b) x y)
    preimage : ∀ b (r : Fibre b ⊎ (Fibre b → ⊥)) → Token r → Fibre b
    preimage b (inl w) _ = w
    preimage b (inr _) ()
    onto : ∀ i → Σ A (λ a → c a ≡ i)
    onto (b , token) with preimage b (test b) token
    ... | a , eq = a , injective eq
