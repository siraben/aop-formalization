{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.FibreMinimumFold where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning
open import AoP.Chapter08.FibreMinimumPrune using (module Prune)
import AoP.Chapter08.ThinningFold as T

-- Exercise 8.11 for cons-list inputs. Each extension first generates
-- an intermediate state, then completes it. Keep the cost minima per
-- enabled state. Local fibre pruning feeds the list thinning theorem;
-- applying min-after-thin gives the original global objective.
module Law {A B I : Set} (Q R : B ← B) (sub : Q ⊆ R)
           (qt : ∀ {a b c} → Q a b → Q b c → Q a c)
           (rt : ∀ {a b c} → R a b → R b c → R a c)
           (E : Pred B) (gen : I ← (A × B)) (finish : B ← I)
           (safe : R ⊓ (finish ∘ finish ˘) ⊆ Q)
           (choose : ∀ i b → finish b i → Σ B λ a → Min R a (λ d → finish d i))
           (match : ∀ {x a b c} → Q a b → (finish ∘ gen) c (x , b) →
                    Σ B λ d → (finish ∘ gen) d (x , a) × Q d c)
           (seed : Pred B) (base : Thin Q seed E) where
  module L = T.Lists Q qt E (finish ∘ gen) match
  enabled : A → Pred B → Pred I
  enabled x X i = Σ B λ b → X b × gen i (x , b)
  table : List A → Pred B
  table [] = seed
  table (x ∷ xs) = Prune.Kept finish (enabled x (table xs)) R Q safe

  prune : ∀ x xs → Thin Q (table (x ∷ xs)) (L.Next x (table xs))
  prune x xs = thin included covered
    where
    module P = Prune finish (enabled x (table xs)) R Q safe
    local = P.sound-pruning (λ i _ → choose i)
    included : ∀ {a} → P.Kept a → L.Next x (table xs) a
    included kept with Thin.subset local kept
    ... | i , (b , xb , g) , f = b , xb , i , f , g
    covered : ∀ a → L.Next x (table xs) a → Σ B λ d → P.Kept d × Q d a
    covered a (b , xb , i , f , g) = Thin.cover local a (i , (b , xb , g) , f)

  module Run = L.Run table base prune
  optimum : ∀ xs {a} → Min R a (table xs) → Min R a (λ d → Fold E (finish ∘ gen) d xs)
  optimum xs = min-after-thin sub rt (Run.correct xs)
