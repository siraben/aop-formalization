{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ParallelExponentialObstruction where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 3.37: the indexing category has two objects and countably
-- many parallel arrows 0 → 1, with only identities besides. A diagram
-- is therefore two sets with a sequence of functions between them.
record Diagram : Set₁ where
  constructor diagram
  field X Y : Set
        edge : Nat → X → Y
open Diagram
record Map (A B : Diagram) : Set where
  constructor natural
  field src : X A → X B
        dst : Y A → Y B
        square : ∀ n x → dst (edge A n x) ≡ edge B n (src x)
open Map
product : Diagram → Diagram → Diagram
product A B = diagram (X A × X B) (Y A × Y B) (λ n p → edge A n (fst p) , edge B n (snd p))
F G : Diagram
F = diagram ⊥ ⊤ (λ n ())
G = diagram Bool Bool (λ _ x → x)
-- Every bit stream gives a diagram with finite components and a map
-- from its product with F to G: ignore the unit at the destination.
test : (Nat → Bool) → Diagram
test bits = diagram ⊤ Bool (λ n _ → bits n)
observe : ∀ bits → Map (product (test bits) F) G
observe bits = natural (λ { (_ , ()) }) fst (λ { n (_ , ()) })

private
  flip : Bool → Bool
  flip true = false
  flip false = true
  apart : ∀ b → flip b ≡ b → ⊥
  apart true ()
  apart false ()
  get : ∀ {A : Set} → List A → A → Nat → A
  get [] d _ = d
  get (a ∷ xs) d 0 = a
  get (a ∷ xs) d (suc n) = get xs d n
  locate : ∀ {A : Set} {x : A} xs d → x ∈ xs → Σ Nat (λ n → get xs d n ≡ x)
  locate (_ ∷ xs) d here = 0 , refl
  locate (_ ∷ xs) d (there p) with locate xs d p
  ... | n , eq = suc n , eq

module Candidate (H : Diagram) (ev : Map (product H F) G)
  (entries : List (X H)) (all : ∀ x → x ∈ entries) where
  decode : X H → Nat → Bool
  decode x n = dst ev (edge H n x , tt)
  -- Only existence of transposes and the destination component of beta
  -- are needed; every exponential must satisfy these conditions.
  Transpose = ∀ bits → Σ (Map (test bits) H) (λ m → ∀ b → dst ev (dst m b , tt) ≡ dst (observe bits) (b , tt))
  impossible : Transpose → ⊥
  impossible curry = reject (locate entries d (all x))
    where d = src (fst (curry (λ _ → false))) tt
          bits = λ n → flip (decode (get entries d n) n)
          m = fst (curry bits)
          x = src m tt
          decoded : ∀ n → bits n ≡ decode x n
          decoded n = back (snd (curry bits) (bits n)) ∙ cong (λ y → dst ev (y , tt)) (square m n tt)
            where back : ∀ {a b : Bool} → a ≡ b → b ≡ a
                  back refl = refl
          reject : Σ Nat (λ n → get entries d n ≡ x) → ⊥
          reject (n , eq) = apart (decode x n) (reverse (cong (λ a → flip (decode a n)) eq) ∙ decoded n)
            where reverse : ∀ {a b : Bool} → a ≡ b → b ≡ a
                  reverse refl = refl
