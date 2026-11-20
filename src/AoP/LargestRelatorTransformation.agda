{-# OPTIONS --safe --without-K #-}
module AoP.LargestRelatorTransformation where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊆_)
open import AoP.LeftDivision using (_＼_)
open import AoP.Shunting using (Id)
open import AoP.MembershipDivisionLaw using (module Law)
open import AoP.LargestMembership using (module Largest)

-- 6.20. In Rel the extra assumption of 6.19 follows by testing
-- naturality against a relation from a singleton naming one input.
data One : Set where point : One
largest-id : ∀ (X : ∀ A → A ← A) → (∀ {A B} (R : B ← A) → X B ∘ R ⊆ R ∘ X A) → ∀ A → X A ⊆ Id
largest-id X lax A {a = a} x = fst (snd (lax name {a = point} (a , x , refl)))
  where name : A ← One
        name b _ = b ≡ a

module Theorem (F G : Set → Set) (LF : ∀ {A B} → B ← A → F B ← F A) (LG : ∀ {A B} → B ← A → G B ← G A)
  (jf : ∀ {A B C} (R : C ← B) (S : B ← A) → LF R ∘ LF S ⊆ LF (R ∘ S))
  (sf : ∀ {A B C} (R : C ← B) (S : B ← A) → LF (R ∘ S) ⊆ LF R ∘ LF S)
  (jg : ∀ {A B C} (R : C ← B) (S : B ← A) → LG R ∘ LG S ⊆ LG (R ∘ S))
  (sg : ∀ {A B C} (R : C ← B) (S : B ← A) → LG (R ∘ S) ⊆ LG R ∘ LG S)
  (f : ∀ A → A ← F A) (g : ∀ A → A ← G A)
  (mf : Law.IdentityLaw F LF jf sf f) (mg : Law.IdentityLaw G LG jg sg g) where
  module FL = Law F LF jf sf f
  module FP = Largest.Proof F LF jf sf f mf largest-id
  module GP = Largest.Proof G LG jg sg g mg largest-id
  Residual = λ A → f A ＼ g A
  Lax : (∀ A → F A ← G A) → Set₁
  Lax T = ∀ {A B} (R : B ← A) → T B ∘ LG R ⊆ LF R ∘ T A
  natural : Lax Residual
  natural {A} R (v , sub , edge) = FL.CompositeLaw.expand (FL.generalize mf) R (g A)
    (λ m → GP.natural R (v , sub m , edge))
  module Bound (T : ∀ A → F A ← G A) (lax : Lax T) where
    select = λ A → f A ∘ T A
    composed : ∀ {A B} (R : B ← A) → select B ∘ LG R ⊆ R ∘ select A
    composed R (v , (u , m , t) , edge) with lax R (v , t , edge)
    ... | w , lifted , t′ with FP.natural R (u , m , lifted)
    ... | a , r , member = a , r , w , member , t′
    maximum : ∀ A → T A ⊆ Residual A
    maximum A t m = GP.Bound.maximum select composed A (_ , m , t)
