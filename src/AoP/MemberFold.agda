{-# OPTIONS --safe --without-K #-}
module AoP.MemberFold where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Complement using (⊥)
open import AoP.Subsequences using (_∈_; here; there)

-- Exercise 6.17. A singleton returns its element. At a cons, choose
-- the head or keep the recursive result. Choosing the head still
-- requires a successful tail fold, supplied by nonemptiness.
data Choose {A : Set} : A ← (A × A) where
  first : ∀ {a b} → Choose a (a , b)
  second : ∀ {a b} → Choose b (a , b)

data Pick {A : Set} : A ← List A where
  single : ∀ {a} → Pick a (a ∷ [])
  step : ∀ {x a b xs} → Choose x (a , b) → Pick b xs → Pick x (a ∷ xs)

sound : ∀ {A} {x : A} {xs} → Pick x xs → x ∈ xs
sound single = here
sound (step first p) = here
sound (step second p) = there (sound p)

head : ∀ {A} (a : A) xs → Pick a (a ∷ xs)
head a [] = single
head a (b ∷ xs) = step first (head b xs)

complete : ∀ {A} {x : A} {xs} → x ∈ xs → Pick x xs
complete {xs = a ∷ xs} here = head a xs
complete (there p) = step second (complete p)

-- For an ordinary relational cons-list fold, soundness forces the nil
-- algebra to have no results. A supposed result on [a] nevertheless
-- contains a result on [] as its tail, contradicting soundness.
impossible : ∀ {A} (a : A) (E : A → Set) (F : A ← (A × A)) →
             Fold E F ⊆ _∈_ → _∈_ ⊆ Fold E F → ⊥
impossible a E F ok all with all {a} {a ∷ []} here
... | cons f tail with ok tail
... | ()
