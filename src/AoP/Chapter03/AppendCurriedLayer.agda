{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.AppendCurriedLayer where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter03.Currying using (curry; apply; ccat)
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter02.Products using ([_,_])

-- §3.5. Derive the function-valued fold algebra for concatenation.
-- In a recursive slot there is already a function awaiting its suffix.
-- Distribution sends the suffix to the selected constructor, and in the
-- cons branch reassociation puts it next to that waiting function.
module At (A : Set) where
  L = List A
  K = L → L
  Layer = ⊤ ⊎ (A × K)
  distribute : Layer × L → (⊤ × L) ⊎ ((A × K) × L)
  distribute (inl u , ys) = inl (u , ys)
  distribute (inr ax , ys) = inr (ax , ys)
  reassociate : (A × K) × L → A × (K × L)
  reassociate ((a , k) , ys) = a , (k , ys)
  attach : A × (K × L) → L
  attach (a , args) = a ∷ apply args
  body : Layer × L → L
  body p = [ snd , (λ q → attach (reassociate q)) ] (distribute p)
  algebra : Layer → K
  algebra = curry body

  nil-law : ∀ ys → algebra (inl tt) ys ≡ ys
  nil-law ys = refl
  cons-law : ∀ a k ys → algebra (inr (a , k)) ys ≡ a ∷ k ys
  cons-law a k ys = refl
  run = ⦅ algebra (inl tt) ∣ (λ a k → algebra (inr (a , k))) ⦆
  -- The operations above simplify to the original curried program.
  agrees : ∀ xs ys → run xs ys ≡ ccat xs ys
  agrees [] ys = nil-law ys
  agrees (a ∷ xs) ys = cons-law a (run xs) ys ∙ cong (a ∷_) (agrees xs ys)
