{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ConditionalFusion where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.CoproductByDuality using (module Dual)

-- §3.4. A conditional first routes its input to a tagged copy and
-- then handles the tag. Isolate the two facts about routing used in
-- the calculation: it commutes with changing inputs, and forgetting
-- the tag recovers the original input. No equality of objects is used.
module In {o h e} (C : Category o h e) where
  open Category C
  open Dual C
  module Given T t (Bool : Obj) where
    open Sum T t
    module Route (tag : ∀ {A} → Hom A Bool → Hom A (A ⊕ A))
      (change : ∀ {A B} (p : Hom B Bool) (k : Hom A B) → tag p ∘ k ≈ map k k ∘ tag (p ∘ k))
      (forget : ∀ {A} (p : Hom A Bool) → cases identity identity ∘ tag p ≈ identity) where
      choose : ∀ {A B} → Hom A Bool → Hom A B → Hom A B → Hom A B
      choose p f g = cases f g ∘ tag p

      -- (3.3): move the final operation into both handlers.
      after : ∀ {A B D} (k : Hom B D) (p : Hom A Bool) (f g : Hom A B) →
        k ∘ choose p f g ≈ choose p (k ∘ f) (k ∘ g)
      after k p f g = transitive (symmetric (assoc _ _ _)) (compose-cong (fusion k f g) reflexive)

      -- (3.4): carry k through the tag, then absorb its two copies.
      before : ∀ {A B D} (k : Hom A B) (p : Hom B Bool) (f g : Hom B D) →
        choose p f g ∘ k ≈ choose (p ∘ k) (f ∘ k) (g ∘ k)
      before k p f g = transitive (assoc _ _ _) (transitive (compose-cong reflexive (change p k))
        (transitive (symmetric (assoc _ _ _)) (compose-cong (absorb f g k k) reflexive)))

      -- (3.5): identical handlers amount to forgetting the tag and
      -- applying f. Use coproduct uniqueness to expose that factorization.
      same : ∀ {A B} (p : Hom A Bool) (f : Hom A B) → choose p f f ≈ f
      same p f = transitive (compose-cong factor reflexive) (transitive (assoc _ _ _)
        (transitive (compose-cong reflexive (forget p)) (unitʳ f)))
        where factor : cases f f ≈ f ∘ cases identity identity
              factor = symmetric (D.Pair.unique _ _ _
                (transitive (assoc _ _ _) (transitive (compose-cong reflexive (cancel-left _ _)) (unitʳ _)))
                (transitive (assoc _ _ _) (transitive (compose-cong reflexive (cancel-right _ _)) (unitʳ _))))
