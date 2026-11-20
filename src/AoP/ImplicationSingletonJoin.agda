{-# OPTIONS --safe --without-K #-}
module AoP.ImplicationSingletonJoin where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊓_; _⊆_)
open import AoP.RelImplication using (_⇒_)
open import AoP.Joins using (⋃)

-- §4.4. For implication, an admissible test X satisfies X ⊓ R ⊆ S.
-- Each edge of X gives an admissible singleton test. Joining these
-- singletons gives the largest test, with a small indexing type.
module Build {A B : Set} (R S : B ← A) where
  one : B → A → B ← A
  one b a y x = (b ≡ y) × (a ≡ x)
  Candidate = Σ B λ b → Σ A λ a → one b a ⊓ R ⊆ S
  branch : Candidate → B ← A
  branch (b , a , _) = one b a
  joined = ⋃ branch

  -- On a joined edge, recover its particular singleton and use the
  -- implication premise (the R edge) to discharge its test.
  apply : joined ⊓ R ⊆ S
  apply (((b , a , safe) , eq) , r) = safe (eq , r)

  largest : (X : B ← A) → X ⊓ R ⊆ S → X ⊆ joined
  largest X law {b} {a} x = (b , a , safe) , refl , refl
    where safe : one b a ⊓ R ⊆ S
          safe ((refl , refl) , r) = law (x , r)

  into : joined ⊆ R ⇒ S
  into j r = apply (j , r)
  out : R ⇒ S ⊆ joined
  out = largest (R ⇒ S) (λ { (h , r) → h r })
