{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelationalCurry where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter05.RelationalProducts using (_⊗_)
private variable A B C : Set

-- Exercise 5.11. For the relational tensor the internal hom from B
-- to A is the set of pairs (a,b). A curried relation offers a pair;
-- evaluation succeeds when the supplied argument matches its b.
eval : A ← ((A × B) × B)
eval a ((a′ , b′) , b) = (a ≡ a′) × (b′ ≡ b)

curry : (A ← (C × B)) → ((A × B) ← C)
curry f (a , b) c = f a (c , b)

apply : ((A × B) ← C) → (A ← (C × B))
apply g = eval ∘ (g ⊗ Id)

read : (g : (A × B) ← C) → ∀ {a b c} → apply g a (c , b) → g (a , b) c
read g (((_ , _) , _) , (refl , refl) , p , refl) = p

write : (g : (A × B) ← C) → ∀ {a b c} → g (a , b) c → apply g a (c , b)
write g {a} {b} p = ((a , b) , b) , (refl , refl) , p , refl

module Universal (f : A ← (C × B)) (g : (A × B) ← C) where
  beta : apply (curry f) ⊆ f
  beta {a} {c , b} p = read (curry f) p
  beta′ : f ⊆ apply (curry f)
  beta′ {a} {c , b} p = write (curry f) p

  unique : apply g ⊆ f → g ⊆ curry f
  unique law {a , b} p = law (write g p)
  unique′ : f ⊆ apply g → curry f ⊆ g
  unique′ law {a , b} p = read g (law p)
