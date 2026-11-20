{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.LocaleRelations where

open import AoP.Common.Prelude

-- Exercise 4.18. A relation assigns a truth value in a frame to each
-- pair of endpoints. Composition joins the grades of all paths through
-- one intermediate point. Order equivalence is mutual inclusion.
record Frame : Set₁ where
  field V : Set
        _≤_ : V → V → Set
        rid : ∀ a → a ≤ a
        chain : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
        meet : V → V → V
        left : ∀ a b → meet a b ≤ a
        right : ∀ a b → meet a b ≤ b
        pair : ∀ {t a b} → t ≤ a → t ≤ b → t ≤ meet a b
        join : ∀ {I : Set} → (I → V) → V
        inject : ∀ {I} (f : I → V) i → f i ≤ join f
        least : ∀ {I t} (f : I → V) → (∀ i → f i ≤ t) → join f ≤ t
        distribute : ∀ {I} (f : I → V) b → meet (join f) b ≤ join (λ i → meet (f i) b)

module Rel (F : Frame) where
  open Frame F
  Rel : Set → Set → Set
  Rel B A = B → A → V
  infix 3 _⊆_
  _⊆_ : ∀ {A B} → Rel B A → Rel B A → Set
  R ⊆ S = ∀ b a → R b a ≤ S b a
  infixr 7 _∘_
  _∘_ : ∀ {A B C} → Rel C B → Rel B A → Rel C A
  (S ∘ R) c a = join (λ b → meet (S c b) (R b a))
  infixr 6 _⊓_
  _⊓_ : ∀ {A B} → Rel B A → Rel B A → Rel B A
  (R ⊓ S) b a = meet (R b a) (S b a)
  rev : ∀ {A B} → Rel B A → Rel A B
  rev R a b = R b a

  -- Distribute the outer meet into the join. For each path via b,
  -- use c itself as witness in the inner converse composite.
  modular : ∀ {A B C} (S : Rel C B) (R : Rel B A) (T : Rel C A) →
            ((S ∘ R) ⊓ T) ⊆ (S ∘ (R ⊓ (rev S ∘ T)))
  modular S R T c a = chain (distribute f (T c a)) (least _ point)
    where f = λ b → meet (S c b) (R b a)
          point : ∀ b → meet (f b) (T c a) ≤ (S ∘ (R ⊓ (rev S ∘ T))) c a
          point b = chain (pair s (pair r inner)) (inject (λ i → meet (S c i) ((R ⊓ (rev S ∘ T)) i a)) b)
            where s = chain (left (f b) (T c a)) (left (S c b) (R b a))
                  r = chain (left (f b) (T c a)) (right (S c b) (R b a))
                  inner = chain (pair s (right (f b) (T c a))) (inject (λ i → meet (S i b) (T i a)) c)
