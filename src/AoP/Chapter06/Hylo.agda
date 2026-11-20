{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Hylo where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- §6.3, for the cons-list shape. A producer may stop or emit a head and
-- a smaller subproblem. It need not terminate everywhere: finite successful
-- runs, not arbitrary solutions of the recursion equation, define the hylo.
module Lists {A B C : Set} (Stop : A → Set) (Emit : (C × A) ← A)
             (Base : B → Set) (Step : B ← (C × B)) where
  data Unfold : List C ← A where
    done : ∀ {a} → Stop a → Unfold [] a
    more : ∀ {c a a′ xs} → Emit (c , a′) a → Unfold xs a′ → Unfold (c ∷ xs) a

  Hylo : B ← A
  Hylo = Fold Base Step ∘ Unfold

  -- One unfolding of the defining equation: either stop on both sides,
  -- or fuse one producer and one consumer step around the same label.
  Φ : (B ← A) → B ← A
  Φ X b a = (Base b × Stop a) ⊎
    (Σ C λ c → Σ A λ a′ → Σ B λ b′ → Emit (c , a′) a × X b′ a′ × Step b (c , b′))

  fold : Φ Hylo ⊆ Hylo
  fold (inl (e , z)) = [] , nil e , done z
  fold (inr (c , a′ , b′ , emit , (xs , f , u) , step)) = c ∷ xs , cons step f , more emit u

  unfold : Hylo ⊆ Φ Hylo
  unfold (_ , nil e , done z) = inl (e , z)
  unfold (_ , cons step f , more emit u) = inr (_ , _ , _ , emit , (_ , f , u) , step)

  -- Peeling the intermediate list establishes leastness by induction;
  -- thus deforestation removes the list without admitting infinite runs.
  least : (X : B ← A) → Φ X ⊆ X → Hylo ⊆ X
  least X k (_ , nil e , done z) = k (inl (e , z))
  least X k (_ , cons step f , more emit u) =
    k (inr (_ , _ , _ , emit , least X k (_ , f , u) , step))
