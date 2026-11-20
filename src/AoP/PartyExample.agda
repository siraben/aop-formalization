{-# OPTIONS --safe --without-K #-}
module AoP.PartyExample where

-- Work through the small company from Party.agda. These two equations
-- are executable checks: Agda computes the invitation lists to prove them.
open import AoP.Prelude
open import AoP.Party using (module Planning)
open import AoP.Trees using (fork; grow; null)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

data Person : Set where Ada Bo Cy : Person
rating : Person → Nat
rating Ada = 8
rating Bo = 5
rating Cy = 5

-- Instantiate the abstract score interface with natural numbers. No
-- score comparison is postulated: compare returns its ordering evidence.
infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤ : ∀ {n} → zero ≤ n
  s≤ : ∀ {n m} → n ≤ m → suc n ≤ suc m

rid : ∀ n → n ≤ n
rid zero = z≤
rid (suc n) = s≤ (rid n)
chain : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
chain z≤ q = z≤
chain (s≤ p) (s≤ q) = s≤ (chain p q)
weaken : ∀ {x y} → x ≤ y → x ≤ suc y
weaken z≤ = z≤
weaken (s≤ p) = s≤ (weaken p)

sum-mono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
sum-mono {b = zero} z≤ q = q
sum-mono {b = suc b} z≤ q = weaken (sum-mono {b = b} z≤ q)
sum-mono (s≤ p) q = s≤ (sum-mono p q)

compare : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
compare zero y = inl z≤
compare (suc x) zero = inr z≤
compare (suc x) (suc y) with compare x y
... | inl p = inl (s≤ p)
... | inr q = inr (s≤ q)

open Planning rating zero _+_ _≤_ rid chain sum-mono compare
reports = grow (fork Bo null) (grow (fork Cy null) null)

-- With no compulsory guests, the two reports together score 10.
ordinary : invitations (fork Ada reports) ≡ Bo ∷ Cy ∷ []
ordinary = refl

-- Requiring Ada costs two points; neither direct report may attend.
mandatory : presidential-invitations Ada reports ≡ Ada ∷ []
mandatory = refl
