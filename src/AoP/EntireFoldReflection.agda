{-# OPTIONS --safe --without-K #-}
module AoP.EntireFoldReflection where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_; _˘)
open import AoP.Shunting using (graph; Id)
open import AoP.DomainPullback using (dom)
open import AoP.RelatorDomain using (module Law)

-- Exercise 5.19 in concrete Rel. The fold equation rewrites H at a
-- constructor into one layer of H followed by the algebra. Entirety of
-- the algebra means the latter step cannot shrink the domain. Thus
-- dom H is a homomorphism from the constructor to itself. Reflection
-- and uniqueness identify that homomorphism with the identity.
module Proof (F : Set → Set) (lift : ∀ {A B} → B ← A → F B ← F A)
             (mono : ∀ {A B} (R S : B ← A) → R ⊆ S → lift R ⊆ lift S)
             (identity : ∀ {A} → lift (Id {A}) ⊆ Id)
             (split : ∀ {A B C} (S : C ← B) (R : B ← A) → lift (S ∘ R) ⊆ lift S ∘ lift R)
             {T B : Set} (roll : F T → T) (alg : B ← F B) (H : B ← T)
             (unfold : H ∘ graph roll ⊆ alg ∘ lift H)
             (fold : alg ∘ lift H ⊆ H ∘ graph roll)
             (entire-alg : ∀ z → Σ B λ b → alg b z)
             (reflection : (D : T ← T) → D ∘ graph roll ⊆ graph roll ∘ lift D →
               graph roll ∘ lift D ⊆ D ∘ graph roll → Id ⊆ D) where
  module Domain = Law.At F lift mono identity split H
  forward : dom H ∘ graph roll ⊆ graph roll ∘ lift (dom H)
  forward {a = t} (_ , (refl , b , h) , refl) with unfold (roll t , h , refl)
  ... | z , a , layer = t , refl , Domain.backward (refl , z , layer)
  backward : graph roll ∘ lift (dom H) ⊆ dom H ∘ graph roll
  backward (_ , refl , test) with Domain.forward test
  ... | refl , z , layer with entire-alg z
  ...   | b , edge with fold (z , edge , layer)
  ...     | _ , h , refl = _ , (refl , b , h) , refl
  all : Id ⊆ dom H
  all = reflection (dom H) forward backward
  entire : Id ⊆ H ˘ ∘ H
  entire {a = x} refl with all {a = x} refl
  ... | _ , b , h = b , h , h
