{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimalTieClass where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.25, with the class represented by the candidate itself.
-- First keep the R-minimal elements. Within the candidate's tie class
-- among these survivors, compare by S. Different R-minimal classes
-- cannot disqualify each other under the combined comparison.
module Law {A : Set} (R S : A ← A) (rr : ∀ a → R a a)
           (tr : ∀ {a b c} → R a b → R b c → R a c) (X : A → Set) where
  Lex : A ← A
  Lex a b = R a b × (R b a → S a b)

  Class : A → A → Set
  Class a b = Min (Test R) b X × (R a b × R b a)

  -- Extracting primary minimality from Lex minimality needs a case
  -- split on the reverse R comparison. A strict predecessor would
  -- automatically precede the candidate under Lex.
  open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
  open import AoP.Chapter04.Complement using (⊥)
  separate : (∀ a b → R a b ⊎ (R a b → ⊥)) → ∀ a → Min (Test Lex) a X → Min (Test S) a (Class a)
  separate decide a (xa , best) = ((xa , primary) , rr a , rr a) , secondary
    where
    absurd : ∀ {B : Set} → ⊥ → B
    absurd ()
    primary : ∀ b → X b → R b a → R a b
    primary b xb ba with decide a b
    ... | inl ab = ab
    ... | inr no = fst (best b xb (ba , λ ab → absurd (no ab)))
    secondary : ∀ b → Class a b → S b a → S a b
    secondary b ((xb , _) , ab , ba) s = snd (best b xb (ba , λ _ → s)) ba

  combine : ∀ a → Min (Test S) a (Class a) → Min (Test Lex) a X
  combine a (((xa , primary) , _) , best) = xa , reverse
    where
    reverse : ∀ b → X b → Lex b a → Lex a b
    reverse b xb (ba , s) = ab , λ _ → best b (((xb , minimal) , ab , ba)) (s ab)
      where
      ab = primary b xb ba
      minimal : ∀ c → X c → R c b → R b c
      minimal c xc cb = tr ba (primary c xc (tr cb ba))
