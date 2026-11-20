{-# OPTIONS --safe --without-K #-}
module AoP.ClosureDiagonal where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.Complement using (_⊔_)
open import AoP.Polynomial using (inl; inr)
open import AoP.Closure using (module Paths)
open import AoP.ClosureSeed using (module After)
open import AoP.MuCalculus using (module Rules)

-- 6.36. Diagonalize the two independent continuations. Holding X
-- fixed, the Y-row allows any number of R edges after Id or S ∘ X.
-- Rolling the leading R* out of the remaining fixed point gives a
-- star whose individual steps are S ∘ R*.
module Law {A : Set} (R S : A ← A) where
  Rel = A ← A
  Incl : Rel → Rel → Set
  Incl = _⊆_
  open Rules Incl (λ p q x → q (p x))
  U = Paths.Star (R ⊔ S)
  B = S ∘ Paths.Star R
  Z = Paths.Star B
  f g : Rel → Rel
  f X = Paths.Star R ∘ X
  g X = Id ⊔ (S ∘ X)
  H : Rel → Rel → Rel
  H X Y = g X ⊔ (R ∘ Y)
  row : ∀ X → Mu (H X) (f (g X))
  row X = record { fold = After.roll (g X) R; unfold = After.expose (g X) R; least = After.least (g X) R }
  diag : Mu (λ X → H X X) U
  Mu.fold diag (inl (inl refl)) = Paths.stop
  Mu.fold diag (inl (inr (_ , s , u))) = Paths.extend (inr s) u
  Mu.fold diag (inr (_ , r , u)) = Paths.extend (inl r) u
  Mu.unfold diag Paths.stop = inl (inl refl)
  Mu.unfold diag (Paths.extend (inl r) u) = inr (_ , r , u)
  Mu.unfold diag (Paths.extend (inr s) u) = inl (inr (_ , s , u))
  Mu.least diag X k = Paths.induction (R ⊔ S) X λ where
    (inl e) → k (inl (inl e))
    (inr (_ , inl r , x)) → k (inr (_ , r , x))
    (inr (_ , inr s , x)) → k (inl (inr (_ , s , x)))

  rolled : Mu (λ X → g (f X)) Z
  Mu.fold rolled (inl refl) = Paths.stop
  Mu.fold rolled (inr (b , s , c , rs , z)) = Paths.extend (b , s , rs) z
  Mu.unfold rolled Paths.stop = inl refl
  Mu.unfold rolled (Paths.extend (b , s , rs) z) = inr (b , s , _ , rs , z)
  Mu.least rolled X k = Paths.induction B X λ where
    (inl e) → k (inl e)
    (inr (c , (b , s , rs) , x)) → k (inr (b , s , c , rs , x))

  fm : ∀ {X Y} → Incl X Y → Incl (f X) (f Y)
  fm k (a , p , x) = a , p , k x
  gm : ∀ {X Y} → Incl X Y → Incl (g X) (g Y)
  gm k (inl e) = inl e
  gm k (inr (a , s , x)) = inr (a , s , k x)
  nested : Mu (λ X → f (g X)) (f Z)
  Mu.fold nested = fm {g (f Z)} {Z} (Mu.fold rolled)
  Mu.unfold nested = fm {Z} {g (f Z)} (Mu.unfold rolled)
  Mu.least nested X k = λ p → k (fm {Z} {g X} (Mu.least rolled (g X) (gm {f (g X)} {X} k)) p)
  module D = Diagonal H (λ X k → λ { (inl p) → inl p ; (inr (a , r , y)) → inr (a , r , k y) }) (λ X → f (g X)) row nested diag
  factor : U ⊆ Paths.Star R ∘ Z
  factor = D.backward
  combine : Paths.Star R ∘ Z ⊆ U
  combine = D.forward
