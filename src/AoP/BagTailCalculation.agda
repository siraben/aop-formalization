{-# OPTIONS --safe --without-K #-}
module AoP.BagTailCalculation where

open import AoP.Prelude
open import AoP.Folds
open import AoP.Relations hiding (cancel)
open import AoP.Shunting using (graph; Id)

-- Exercise 5.28, the bag calculation. Parameterize the proof by the
-- bag algebra: equality of bags, not equality of lists, specifies a
-- permutation. Surjectivity supplies a representative of each bag.
module Law {A Bag : Set} (empty : Bag) (add : A → Bag → Bag) where
  bagify = ⦅ empty ∣ add ⦆
  B = graph bagify
  perm = B ˘ ∘ B

  module Onto (represent : ∀ b → Σ (List A) λ xs → bagify xs ≡ b) where
    cancel : B ∘ B ˘ ⊆ Id
    cancel (_ , refl , refl) = refl
    restore : Id ⊆ B ∘ B ˘
    restore {b} refl with represent b
    ... | xs , eq = xs , eq , eq

    -- Insert the identity B ∘ B˘ at the bag of the tail. Reading its
    -- intermediate list supplies the preliminary tail permutation.
    insert-tail : ∀ {x xs ys} → perm ys (x ∷ xs) → Σ (List A) λ zs → perm zs xs × perm ys (x ∷ zs)
    insert-tail {x} {xs} (b , p , q) with restore {bagify xs} refl
    ... | zs , eq , _ = zs , (bagify xs , eq , refl) , b , p , (cong (add x) eq ∙ q)

    remove-tail : ∀ {x xs ys} → (Σ (List A) λ zs → perm zs xs × perm ys (x ∷ zs)) → perm ys (x ∷ xs)
    remove-tail {x} {xs} (zs , (b , u , v) , c , p , q) = c , p , (cong (add x) same ∙ q)
      where same : bagify xs ≡ bagify zs
            same = v ∙ back u
              where back : ∀ {a b : Bag} → a ≡ b → b ≡ a
                    back refl = refl
