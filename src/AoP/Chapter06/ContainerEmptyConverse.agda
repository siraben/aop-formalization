{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ContainerEmptyConverse where

open import AoP.Common.Prelude
open import AoP.Chapter06.ContainerEmpty using (module Law)
open import AoP.Chapter04.Complement using (⊥)

-- 6.21: calibrate the Boolean hypothesis in the container model.
-- A single shape with P positions gives F A = ⊤ × (P → A).
-- Emptiness at ⊥ says ¬¬P, whereas a member of the unit-labelled
-- container exhibits an actual position. Thus even this one-shape
-- family forces double-negation elimination if the converse is uniform.
Converse : Set₁
Converse = (S : Set) (Pos : S → Set) → (Law.F S Pos ⊥ → ⊥) → Law.Entire S Pos

necessary : Converse → (P : Set) → ((P → ⊥) → ⊥) → P
necessary law P nn = fst (snd (law ⊤ (λ _ → P) empty {A = ⊤} (tt , λ _ → tt)))
  where empty : Law.F ⊤ (λ _ → P) ⊥ → ⊥
        empty (_ , refute) = nn refute

sufficient : ((P : Set) → ((P → ⊥) → ⊥) → P) → Converse
sufficient dne S Pos empty (s , labels) = labels i , (i , refl)
  where i : Pos s
        i = dne (Pos s) (λ no → empty (s , no))
