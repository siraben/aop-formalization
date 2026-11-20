{-# OPTIONS --safe --without-K #-}
module AoP.InverseNaturality where

open import AoP.Prelude
open import AoP.DistributiveHoms using (Bijection)
open Bijection

-- When reversing the currying or coproduct step of a hom-set
-- calculation we need not assume a second naturality square. Insert
-- the inverse via the section law, commute the forward square, and
-- cancel with the retraction law.
module Square {X Y X′ Y′ : Set} (b : Bijection X Y) (b′ : Bijection X′ Y′)
              (u : X → X′) (v : Y → Y′)
              (forward : ∀ x → to b′ (u x) ≡ v (to b x)) where
  private
    back : ∀ {T : Set} {x y : T} → x ≡ y → y ≡ x
    back refl = refl

  inverse : ∀ y → from b′ (v y) ≡ u (from b y)
  inverse y = begin
    from b′ (v y) ≡⟨ cong (λ z → from b′ (v z)) (back (section b y)) ⟩
    from b′ (v (to b (from b y))) ≡⟨ cong (from b′) (back (forward (from b y))) ⟩
    from b′ (to b′ (u (from b y))) ≡⟨ retract b′ (u (from b y)) ⟩
    u (from b y) ∎
