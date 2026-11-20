{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.RelDifference where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥; ¬_; _⊔_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
private variable A B : Set

-- Exercise 4.30, concrete relations. Membership in R − S carries an
-- R-edge and a refutation of its S-membership. To recover a cover by
-- S or X, decide only membership in S at the endpoints in question.
infixl 7 _−_
_−_ : (B ← A) → (B ← A) → B ← A
R − S = R ⊓ (¬ S)
Decides : (B ← A) → Set
Decides S = ∀ b a → S b a ⊎ (¬ S) b a

remove : (R S X : B ← A) → R ⊆ S ⊔ X → R − S ⊆ X
remove R S X cover (r , ns) with cover r
... | inr x = x
... | inl s with ns s
...   | ()
cover : (R S X : B ← A) → Decides S → R − S ⊆ X → R ⊆ S ⊔ X
cover R S X decide incl {b} {a} r with decide b a
... | inl s = inl s
... | inr ns = inr (incl (r , ns))

module Laws (R S T : B ← A) where
  empty : B ← A
  empty _ _ = ⊥
  unit : R − empty ⊆ R
  unit = fst
  unit′ : R ⊆ R − empty
  unit′ r = r , λ ()

  trim : Decides R → R ⊔ S ⊆ R ⊔ (S − R)
  trim dec (inl r) = inl r
  trim dec {b} {a} (inr s) = cover S R (S − R) dec (λ p → p) s
  untrim : R ⊔ (S − R) ⊆ R ⊔ S
  untrim (inl r) = inl r
  untrim (inr (s , _)) = inr s

  successive : R − (S ⊔ T) ⊆ (R − S) − T
  successive (r , n) = (r , (λ s → n (inl s))) , λ t → n (inr t)
  combine : (R − S) − T ⊆ R − (S ⊔ T)
  combine ((r , ns) , nt) = r , λ { (inl s) → ns s ; (inr t) → nt t }

  distribute : (R ⊔ S) − T ⊆ (R − T) ⊔ (S − T)
  distribute (inl r , nt) = inl (r , nt)
  distribute (inr s , nt) = inr (s , nt)
  collect : (R − T) ⊔ (S − T) ⊆ (R ⊔ S) − T
  collect (inl (r , nt)) = inl r , nt
  collect (inr (s , nt)) = inr s , nt
