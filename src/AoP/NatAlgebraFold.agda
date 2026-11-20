{-# OPTIONS --safe --without-K #-}
module AoP.NatAlgebraFold where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Functors using (Functor)
open import AoP.Categories using (Fun)
open import AoP.AlgebraCategory using (module For)
open import AoP.UniversalObjects using (module Universal)
open import AoP.Naturals using (foldn; foldn-unique)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §2.6. One layer of a natural number either marks zero or contains
-- its predecessor. Mapping acts only on that predecessor.
layer : Functor Fun Fun
Functor.F₀ layer A = ⊤ ⊎ A
Functor.F₁ layer f (inl u) = inl u
Functor.F₁ layer f (inr a) = inr (f a)
Functor.resp layer p (inl u) = refl
Functor.resp layer p (inr a) = cong inr (p a)
Functor.identity layer (inl u) = refl
Functor.identity layer (inr a) = refl
Functor.composition layer g f (inl u) = refl
Functor.composition layer g f (inr a) = refl

open For Fun layer
module U = Universal algebras
roll : ⊤ ⊎ Nat → Nat
roll (inl _) = zero
roll (inr n) = suc n
numbers = alg Nat roll

-- Read the homomorphism square once at each injection. Conversely
-- these two equations cover every possible layer, so they suffice.
module Calculate {A : Set} (act : ⊤ ⊎ A → A) (h : Nat → A) where
  Square = ∀ x → h (roll x) ≡ act (Functor.F₁ layer h x)
  Base = h zero ≡ act (inl tt)
  Step = ∀ n → h (suc n) ≡ act (inr (h n))
  cancel : Square → Base × Step
  cancel eq = eq (inl tt) , (λ n → eq (inr n))
  combine : Base × Step → Square
  combine (base , step) (inl tt) = base
  combine (base , step) (inr n) = step n

-- Initiality now uses the Chapter 1 iterator as the actual carrier
-- map. Uniqueness is precisely induction on the two extracted clauses.
initial : U.Initial numbers
Map.arrow (U.Initial.leave initial (alg A act)) = foldn (act (inl tt)) (λ a → act (inr a))
Map.square (U.Initial.leave initial (alg A act)) = Calculate.combine act _ (refl , (λ _ → refl))
U.Initial.unique initial {alg A act} (hom h eq) = foldn-unique h _ _ (fst clauses) (snd clauses)
  where clauses = Calculate.cancel act h eq
