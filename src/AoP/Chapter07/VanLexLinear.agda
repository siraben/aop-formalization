{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanLexLinear where

open import AoP.Common.Prelude
open import AoP.Chapter07.VanLexOrder using (module Order)
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 7.57. Scan the first blocks against the same flattened
-- input. Either one ends strictly earlier or they end together and
-- leave identical suffixes. No equality test on transactions is needed.
module Compare (A : Set) where
  open Law A using (Prefix; keep; empty)
  open Order A
  data Cut (x y u v : List A) : Set where
    earlier : Prefix x y → (Prefix y x → ⊥) → Cut x y u v
    later : Prefix y x → (Prefix x y → ⊥) → Cut x y u v
    together : x ≡ y → u ≡ v → Cut x y u v

  cut : ∀ x y u v → x ++ u ≡ y ++ v → Cut x y u v
  cut [] [] u v eq = together refl eq
  cut [] (b ∷ y) u v eq = earlier empty (λ ())
  cut (a ∷ x) [] u v eq = later empty (λ ())
  cut (a ∷ x) (b ∷ y) u v eq with head-eq eq | tail-eq eq
    where head-eq : ∀ {a b : A} {as bs} → a ∷ as ≡ b ∷ bs → a ≡ b
          head-eq refl = refl
          tail-eq : ∀ {a b : A} {as bs} → a ∷ as ≡ b ∷ bs → as ≡ bs
          tail-eq refl = refl
  ... | refl | eq′ with cut x y u v eq′
  ...   | earlier p no = earlier (keep a p) (λ q → no (tails q))
  ...   | later p no = later (keep a p) (λ q → no (tails q))
  ...   | together refl e = together refl e

  flatten : Blocks → List A
  flatten [] = []
  flatten (x ∷ xs) = x ++ flatten xs
  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()
  total : ∀ xs ys → flatten xs ≡ flatten ys → Q xs ys ⊎ Q ys xs
  total [] ys eq = inl tt
  total (x ∷ xs) [] eq = inr tt
  total (x ∷ xs) (y ∷ ys) eq with cut x y (flatten xs) (flatten ys) eq
  ... | earlier p no = inl (p , λ q → absurd (no q))
  ... | later p no = inr (p , λ q → absurd (no q))
  ... | together refl e with total xs ys e
  ...   | inl q = inl (reflP x , λ _ → q)
  ...   | inr q = inr (reflP x , λ _ → q)
