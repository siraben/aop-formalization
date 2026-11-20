{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.Relations where

open import AoP.Common.Prelude
private variable A B C D : Set

-- Target first: R : B ← A relates output b to input a.
infix 2 _←_
infix 3 _⊆_
infixr 7 _∘_
infixr 6 _⊓_
infix 9 _˘
_←_ : Set → Set → Set₁
B ← A = B → A → Set

_⊆_ : (B ← A) → (B ← A) → Set
R ⊆ S = ∀ {b a} → R b a → S b a

_∘_ : (C ← B) → (B ← A) → (C ← A)
_∘_ {B = B} S R c a = Σ B λ b → S c b × R b a

_˘ : (B ← A) → (A ← B)
(R ˘) a b = R b a

_⊓_ : (B ← A) → (B ← A) → (B ← A)
(R ⊓ S) b a = R b a × S b a

-- Each proof acts directly on a witness of membership.
modular : (S : C ← B) (R : B ← A) (T : C ← A) →
          (S ∘ R) ⊓ T ⊆ S ∘ (R ⊓ (S ˘ ∘ T))
modular S R T ((b , s , r) , t) = b , s , r , _ , s , t

infixr 7 _／_
_／_ : (C ← A) → (B ← A) → (C ← B)
(T ／ R) c b = ∀ {a} → R b a → T c a

residuate : (S : C ← B) (R : B ← A) (T : C ← A) →
            (S ∘ R ⊆ T) → (S ⊆ T ／ R)
residuate S R T k s r = k (_ , s , r)

cancel : (S : C ← B) (R : B ← A) (T : C ← A) →
         (S ⊆ T ／ R) → (S ∘ R ⊆ T)
cancel S R T k (_ , s , r) = k s r

-- Relational catamorphism for cons-lists (section 5.5).
data Fold {A B : Set} (E : B → Set) (F : B ← (A × B)) : B ← List A where
  nil  : ∀ {b} → E b → Fold E F b []
  cons : ∀ {x xs b c} → F c (x , b) → Fold E F b xs → Fold E F c (x ∷ xs)
