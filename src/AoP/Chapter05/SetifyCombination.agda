{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SetifyCombination where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_; concat)
open import AoP.Chapter05.ListSetify using (setify)
open import AoP.Chapter04.Power using (_≐_)
open import AoP.Chapter05.TransposeCombinations using (cup)
open import AoP.Chapter05.Subsequences using (_∈_; merge; split; here; there; image; preimage)
open import AoP.Chapter03.ListStrength using (cpr)
open import AoP.Chapter02.Polynomial using (inl; inr)
private variable A B : Set

-- §5.6. These three intermediate identities explain the list operations
-- implementing union, indexed union and pairing with a fixed element.
append : (xs ys : List A) → setify (xs ++ ys) ≐ cup (setify xs , setify ys)
append xs ys = (λ _ → split xs ys) , (λ _ → merge xs ys)

member-of-member : List (List A) → A → Set
member-of-member {A} xss a = Σ (List A) λ xs → (xs ∈ xss) × (a ∈ xs)

flatten : (xss : List (List A)) → setify (concat xss) ≐ member-of-member xss
flatten [] = (λ { _ () }) , (λ { _ (_ , () , _) })
flatten (xs ∷ xss) = out , into
  where
  out : ∀ a → a ∈ concat (xs ∷ xss) → member-of-member (xs ∷ xss) a
  out a p with split xs (concat xss) p
  ... | inl q = xs , here , q
  ... | inr q with fst (flatten xss) a q
  ...   | ys , m , n = ys , there m , n
  into : ∀ a → member-of-member (xs ∷ xss) a → a ∈ concat (xs ∷ xss)
  into a (_ , here , q) = merge xs (concat xss) (inl q)
  into a (ys , there m , n) = merge xs (concat xss) (inr (snd (flatten xss) a (ys , m , n)))

pairing : (a : A) (bs : List B) → setify (cpr (a , bs)) ≐ (λ p → (fst p ≡ a) × (snd p ∈ bs))
pairing a bs = out , into
  where
  out : ∀ p → p ∈ cpr (a , bs) → (fst p ≡ a) × (snd p ∈ bs)
  out p m with preimage (a ,_) bs m
  ... | b , q , refl = refl , q
  into : ∀ p → (fst p ≡ a) × (snd p ∈ bs) → p ∈ cpr (a , bs)
  into (_ , _) (refl , q) = image (a ,_) q
