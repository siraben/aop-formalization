{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.TypeLiftConverse where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §5.5. The constructor isomorphism lets us write the defining fold
-- equation in rolled form: t = rollB ∘ layer(t,r) ∘ rollA˘.
-- Reverse this equation. The outer constructors swap roles and the
-- binary relator reverses both arguments. Thus t˘ solves the defining
-- equation for lifting r˘; fold uniqueness identifies the result.
module Proof {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  private
    turn : ∀ {A B} {r s : Hom A B} → r ≈ s → rev r ≈ rev s
    turn eq = antisym (rev-mono (respect eq)) (rev-mono (respect (symmetric eq)))
  -- Move an invertible input constructor across the fold equation.
  -- The two directions use opposite inverse laws, so callers can see
  -- exactly where constructor invertibility enters the calculation.
  module Roll {I T Y} (a : Hom I T) (t : Hom T Y) (step : Hom I Y) where
    roll : (a ∘ rev a) ≈ identity → (t ∘ a) ≈ step → t ≈ (step ∘ rev a)
    roll onto square = transitive (symmetric (unitʳ t)) (transitive
      (compose-cong reflexive (symmetric onto)) (transitive (symmetric (assoc _ _ _)) (compose-cong square reflexive)))
    unroll : (rev a ∘ a) ≈ identity → t ≈ (step ∘ rev a) → (t ∘ a) ≈ step
    unroll one eq = transitive (compose-cong eq reflexive) (transitive (assoc _ _ _)
      (transitive (compose-cong reflexive one) (unitʳ step)))
  module At {A B TA TB FA FB} (a : Hom FA TA) (b : Hom FB TB) (r : Hom A B)
    (layer : Hom TA TB → Hom A B → Hom FA FB)
    (back : Hom TB TA → Hom B A → Hom FB FA)
    (reverse-layer : ∀ t → rev (layer t r) ≈ back (rev t) (rev r)) where
    module Lift (t : Hom TA TB) (eq : t ≈ (b ∘ (layer t r ∘ rev a))) where
      reversed : rev t ≈ (a ∘ (back (rev t) (rev r) ∘ rev b))
      reversed = transitive (turn eq) (transitive (flip _ _) (transitive
        (compose-cong (transitive (flip _ _) (compose-cong (invol a) (reverse-layer t))) reflexive) (assoc _ _ _)))
      preserve : (u : Hom TB TA) → (∀ x → x ≈ (a ∘ (back x (rev r) ∘ rev b)) → x ≈ u) → rev t ≈ u
      preserve u unique = unique _ reversed
    -- Start with ordinary fold computation and finish with ordinary
    -- fold uniqueness in the reverse direction. Reassociate the
    -- constructor composites at the interface to the rolled proof.
    from-fold : (t : Hom TA TB) (u : Hom TB TA) → (a ∘ rev a) ≈ identity → (rev b ∘ b) ≈ identity →
      (t ∘ a) ≈ (b ∘ layer t r) → (∀ x → (x ∘ b) ≈ (a ∘ back x (rev r)) → x ≈ u) → rev t ≈ u
    from-fold t u onto one square unique = unique _ (Roll.unroll b _ _ one
      (transitive (Lift.reversed t rolled) (symmetric (assoc _ _ _))))
      where rolled = transitive (Roll.roll a t _ onto square) (assoc _ _ _)
