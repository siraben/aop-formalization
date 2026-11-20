{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.AppendOptimal where

open import AoP.Common.Prelude
open import AoP.Chapter09.Bracketing using (module Append)
open import AoP.Chapter09.BracketSpine using (leaves)
open import AoP.Chapter01.Trees using (Tree; bin; tip)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; z≤; rid; sum-mono; chain)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- For list append, charge one unit for every cell of the left argument.
-- Right association traverses each operand except the last exactly once.
-- Show that this cost (bill) is a lower bound for *every* bracketing.
bill : List Nat → Nat
bill [] = 0
bill (a ∷ []) = 0
bill (a ∷ b ∷ xs) = a + bill (b ∷ xs)

private
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc zero b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)

  back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  back refl = refl

  ++assoc : ∀ (xs ys zs : List Nat) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++assoc [] ys zs = refl
  ++assoc (x ∷ xs) ys zs = cong (x ∷_) (++assoc xs ys zs)

  nonempty : ∀ (t : Tree Nat) → Σ Nat λ a → Σ (List Nat) λ xs → leaves t ≡ a ∷ xs
  nonempty (tip a) = a , [] , refl
  nonempty (bin l r) with nonempty l
  ... | a , xs , eq = a , xs ++ leaves r , cong (_++ leaves r) eq

  prepend : ∀ t b xs → bill (leaves t ++ (b ∷ xs)) ≡ Append.size t + bill (b ∷ xs)
  prepend (tip a) b xs = refl
  prepend (bin l r) b xs with nonempty r
  ... | c , ys , eq = begin
    _ ≡⟨ cong bill (++assoc (leaves l) (leaves r) (b ∷ xs)) ⟩
    _ ≡⟨ cong (λ zs → bill (leaves l ++ (zs ++ (b ∷ xs)))) eq ⟩
    _ ≡⟨ prepend l c (ys ++ (b ∷ xs)) ⟩
    _ ≡⟨ finish ⟩
    _ ∎
    where
    finish : Append.size l + bill (c ∷ (ys ++ (b ∷ xs))) ≡ (Append.size l + Append.size r) + bill (b ∷ xs)
    finish = cong (Append.size l +_) (cong bill (back (cong (_++ (b ∷ xs)) eq)) ∙ prepend r b xs) ∙ back (assoc (Append.size l) (Append.size r) (bill (b ∷ xs)))

bound : ∀ t → bill (leaves t) ≤ Append.cost t
bound (tip a) = z≤
bound (bin l r) with nonempty r | bound r
... | b , xs , eq | cheap rewrite eq | prepend l b xs =
  sum-mono (rid _) (chain cheap (sum-mono {a = 0} {b = Append.cost l} z≤ (rid _)))

right : Nat → List Nat → Tree Nat
right a [] = tip a
right a (b ∷ xs) = bin (tip a) (right b xs)

spells : ∀ a xs → leaves (right a xs) ≡ a ∷ xs
spells a [] = refl
spells a (b ∷ xs) = cong (a ∷_) (spells b xs)

attains : ∀ a xs → Append.cost (right a xs) ≡ bill (a ∷ xs)
attains a [] = refl
attains a (b ∷ xs) = cong (a +_) (attains b xs)

optimal : ∀ a xs t → leaves t ≡ a ∷ xs → Append.cost (right a xs) ≤ Append.cost t
optimal a xs t eq rewrite attains a xs | back eq = bound t
