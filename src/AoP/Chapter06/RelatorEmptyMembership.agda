{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.RelatorEmptyMembership where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter06.MembershipDivisionLaw using (module Law)

-- Exercise 6.21 for abstract liftings on concrete Rel. Factor the empty
-- column A ← ⊤ through ⊥. With no members, every member of v lies in
-- that composite vacuously. The expansion law then supplies a value of
-- F ⊥ as the intermediate point, contradicting the emptiness hypothesis.
module Proof (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (join : ∀ {A B C} (R : C ← B) (S : B ← A) → L R ∘ L S ⊆ L (R ∘ S))
  (split : ∀ {A B C} (R : C ← B) (S : B ← A) → L (R ∘ S) ⊆ L R ∘ L S)
  (member : ∀ A → A ← F A) where
  open Law F L join split member
  Entire = ∀ (A : Set) (v : F A) → Σ A (λ a → member A a v)
  forward : Entire → F ⊥ → ⊥
  forward all v = fst (all ⊥ v)
  Member : ∀ A → F A → Set
  Member A v = Σ A (λ a → member A a v)
  NoVacant = ∀ A (v : F A) → (Member A v → ⊥) → ⊥

  -- The factorization itself needs no classical elimination. A vacant
  -- fibre would produce an intermediate F ⊥ value.
  no-vacant : IdentityLaw → (F ⊥ → ⊥) → NoVacant
  no-vacant law empty A v none = empty (fst (CompositeLaw.expand (generalize law) R S {b = v} {a = tt} (vacant none)))
    where R : A ← ⊥
          R a ()
          S : ⊥ ← ⊤
          S () x
          vacant : (Σ A (λ a → member A a v) → ⊥) → Columns (R ∘ S) v tt
          vacant none {x} m with none (x , m)
          ... | ()

  -- Conversely a structure over ⊥ cannot supply a member. Thus
  -- emptiness of F ⊥ is constructively equivalent to NoVacant.
  empty-from-no-vacant : NoVacant → F ⊥ → ⊥
  empty-from-no-vacant nv v = nv ⊥ v fst

  -- Extract actual witnesses only at the fibres where they are used.
  -- A local decision procedure suffices, even without global DNE.
  stable-backward : IdentityLaw → (∀ A v → ((Member A v → ⊥) → ⊥) → Member A v) →
                    (F ⊥ → ⊥) → Entire
  stable-backward law stable empty A v = stable A v (no-vacant law empty A v)
  backward : IdentityLaw → (∀ P → ((P → ⊥) → ⊥) → P) → (F ⊥ → ⊥) → Entire
  backward law dne = stable-backward law (λ A v → dne (Member A v))
