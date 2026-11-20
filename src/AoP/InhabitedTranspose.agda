{-# OPTIONS --safe --without-K #-}
module AoP.InhabitedTranspose where

open import AoP.Prelude
open import AoP.Power using (ℙ; Λ; _≐_)
open import AoP.Relations
open import AoP.Shunting using (Id)

-- Exercise 4.45. To transpose into nonempty subsets, restrict the
-- source relations to entire ones. Each input then has an output to
-- witness nonemptiness of its fibre. Two represented subsets agree
-- when their memberships agree, regardless of the chosen witness.
record Inhabited (B : Set) : Set₁ where
  constructor inhabited
  field members : ℙ B
        witness : Σ B members
open Inhabited

module Law {A B : Set} (R : B ← A) where
  Entire = Id ⊆ R ˘ ∘ R
  Represents : (A → Inhabited B) → Set
  Represents f = ∀ a → members (f a) ≐ Λ R a

  transpose : Entire → A → Inhabited B
  transpose total a with total {a} {a} refl
  ... | b , r , _ = inhabited (Λ R a) (b , r)

  exact : (total : Entire) → Represents (transpose total)
  exact total a with total {a} {a} refl
  ... | b , r , _ = (λ _ x → x) , (λ _ x → x)

  necessary : (f : A → Inhabited B) → Represents f → Entire
  necessary f law {a} refl with witness (f a)
  ... | b , p = let r = fst (law a) b p in b , r , r

  unique : (f g : A → Inhabited B) → Represents f → Represents g →
           ∀ a → members (f a) ≐ members (g a)
  unique f g l r a = (λ b x → snd (r a) b (fst (l a) b x)) ,
                     (λ b x → snd (l a) b (fst (r a) b x))
