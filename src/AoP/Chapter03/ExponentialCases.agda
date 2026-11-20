{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ExponentialCases where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.Products using ([_,_])
open import AoP.Chapter04.Complement using (⊥)
private variable A B C : Set

-- §3.5, exercises 3.33–34 in Fun. Read A^B as a table of A-values
-- indexed by B. An empty table carries no information, a singleton
-- table stores one value, and a tagged index splits a table in two.
empty-table : (⊥ → A) → ⊤
empty-table _ = tt
from-empty : ⊤ → ⊥ → A
from-empty tt ()
empty-section : (u : ⊤) → empty-table {A = A} (from-empty u) ≡ u
empty-section tt = refl
empty-recover : (f : ⊥ → A) (i : ⊥) → from-empty (empty-table f) i ≡ f i
empty-recover f ()

single : (⊤ → A) → A
single f = f tt
constant : A → ⊤ → A
constant a _ = a
single-section : (a : A) → single (constant a) ≡ a
single-section a = refl
single-recover : (f : ⊤ → A) (i : ⊤) → constant (single f) i ≡ f i
single-recover f tt = refl

split : (B ⊎ C → A) → (B → A) × (C → A)
split f = (λ b → f (inl b)) , (λ c → f (inr c))
join : (B → A) × (C → A) → B ⊎ C → A
join (l , r) = [ l , r ]
joined : (f : B ⊎ C → A) (i : B ⊎ C) → join (split f) i ≡ f i
joined f (inl _) = refl
joined f (inr _) = refl
split-left : (p : (B → A) × (C → A)) (b : B) → fst (split (join p)) b ≡ fst p b
split-left p b = refl
split-right : (p : (B → A) × (C → A)) (c : C) → snd (split (join p)) c ≡ snd p c
split-right p c = refl

-- A global element of the function space (B → A) stores an entire
-- function as the singleton's only value. Read it back by evaluation.
name : (B → A) → ⊤ → B → A
name = constant
apply-name : (f : B → A) (b : B) → single (name f) b ≡ f b
apply-name f b = refl
name-apply : (g : ⊤ → B → A) (i : ⊤) (b : B) → name (single g) i b ≡ g i b
name-apply g tt b = refl
