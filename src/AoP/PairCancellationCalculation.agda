{-# OPTIONS --safe --without-K #-}
module AoP.PairCancellationCalculation where

open import AoP.Prelude
open import AoP.Relations hiding (cancel)
open import AoP.Shunting using (graph)
open import AoP.RelationalPairing using (pair; branches)
open import AoP.RelationalProducts using (_⊗_)
open import AoP.PairAbsorptionCalculation using (module Relation)

-- §5.2 (5.8). The converse of a pairing asks for a common source
-- for both of its outputs. Factor this check through the diagonal:
-- independent converse branches first choose sources, then the
-- diagonal checks that those sources coincide.
module At {A B C D : Set} (R : B ← A) (S : C ← A) (X : B ← D) (Y : C ← D) where
  diag : (A × A) ← A
  diag = graph (λ a → a , a)
  Start = pair R S ˘ ∘ pair X Y
  Via = diag ˘ ∘ ((R ˘ ⊗ S ˘) ∘ pair X Y)
  Joined = diag ˘ ∘ pair (R ˘ ∘ X) (S ˘ ∘ Y)
  End = (R ˘ ∘ X) ⊓ (S ˘ ∘ Y)

  factor : Start ⊆ Via
  factor (bc , (r , s) , xy) = (_ , _) , refl , bc , (r , s) , xy
  unfactor : Via ⊆ Start
  unfactor (_ , refl , bc , (r , s) , xy) = bc , (r , s) , xy
  absorb : Via ⊆ Joined
  absorb (aa , eq , step) = aa , eq , branches (R ˘) (S ˘) X Y step
  expand : Joined ⊆ Via
  expand (aa , eq , paths) = aa , eq , Relation.absorb (R ˘) (S ˘) X Y paths
  -- Eliminating equality with (a,a) puts both paths at the same a;
  -- conversely that shared endpoint supplies the diagonal witness.
  cancel : Joined ⊆ End
  cancel (_ , refl , paths) = paths
  restore : End ⊆ Joined
  restore paths = (_ , _) , refl , paths
  forward : Start ⊆ End
  forward h = cancel (absorb (factor h))
  backward : End ⊆ Start
  backward h = unfactor (expand (restore h))
