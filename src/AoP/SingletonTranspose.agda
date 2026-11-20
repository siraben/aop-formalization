{-# OPTIONS --safe --without-K #-}
module AoP.SingletonTranspose where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.Power using (ℙ; Λ; ℰ; _≐_)
private variable A B C : Set

-- Exercise 4.46. The transpose of identity sends an element to its
-- singleton. Evaluating equality of singleton predicates at the first
-- element recovers equality of the elements, hence left cancellation.
unit : A → ℙ A
unit = Λ Id

injective : (x y : A) → unit x ≐ unit y → x ≡ y
injective x y eq = fst eq x refl

monic : (f g : C → A) → (∀ c → unit (f c) ≐ unit (g c)) → ∀ c → f c ≡ g c
monic f g law c = injective (f c) (g c) (law c)

-- Exercise 4.47. The direct image of a singleton is the corresponding
-- fibre. For an arbitrary input subset, collect all fibres selected by
-- that subset, then take their union. Use extensional subset equality
-- to avoid equating functions or resizing the universe of predicates.
singleton-image : (R : B ← A) (a : A) → ℰ R (unit a) ≐ Λ R a
singleton-image R a = (λ { _ (_ , r , refl) → r }) , (λ _ r → a , r , refl)

module Union {A B : Set} (R : B ← A) (X : ℙ A) where
  selected : ℙ B → Set
  selected Y = Σ A λ a → X a × (Λ R a ≐ Y)
  joined : B → Set₁
  joined b = Σ (ℙ B) λ Y → selected Y × Y b

  collect : ∀ b → joined b → ℰ R X b
  collect b (Y , (a , x , eq) , y) = a , snd eq b y , x
  distribute : ∀ b → ℰ R X b → joined b
  distribute b (a , r , x) = Λ R a , (a , x , ((λ _ p → p) , (λ _ p → p))) , r
