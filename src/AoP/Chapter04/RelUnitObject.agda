{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.RelUnitObject where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Chapter04.Shunting using (Id; graph)

-- §4.3. Characterize unit objects in concrete Rel. Identity is the
-- largest endorelation on U, and every input type admits an entire
-- relation to U. Testing these conditions on the full relation and
-- on a singleton input shows that U has exactly one inhabitant.
Full : ∀ {A B : Set} → B ← A
Full _ _ = ⊤
record UnitObject (U : Set) : Set₁ where
  field scalar : (R : U ← U) → R ⊆ Id
        cover : ∀ (A : Set) → Σ (U ← A) (λ p → Id ⊆ p ˘ ∘ p)

module Extract {U : Set} (unit : UnitObject U) where
  point : U
  point = fst (snd (UnitObject.cover unit ⊤) {a = tt} refl)
  same : ∀ x y → x ≡ y
  same x y = UnitObject.scalar unit Full {b = x} {a = y} tt

module Build {U : Set} (u : U) (same : ∀ x y → x ≡ y) where
  p : ∀ {A : Set} → U ← A
  p = graph (λ _ → u)
  unit : UnitObject U
  UnitObject.scalar unit R {b} {a} edge = same b a
  UnitObject.cover unit A = p , (λ { refl → u , refl , refl })

  -- Every relation factors by inclusion through the two constant maps:
  -- the intermediate witness is u, regardless of either endpoint.
  largest : ∀ {A B : Set} (R : B ← A) → R ⊆ p ˘ ∘ p
  largest R edge = u , refl , refl

singleton : UnitObject ⊤
singleton = Build.unit tt (λ _ _ → refl)
