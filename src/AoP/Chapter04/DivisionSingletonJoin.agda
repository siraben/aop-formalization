{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.DivisionSingletonJoin where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.LeftDivision using (_＼_)
open import AoP.Chapter04.Joins using (⋃)

-- §4.4. To construct the join defining left division in concrete Rel,
-- singleton test relations suffice. An arbitrary admissible relation
-- contributes each of its edges separately. Indexing by endpoint pairs
-- and their local tests keeps the entire join in the small universe.
module Build {A B C : Set} (R : C ← A) (S : C ← B) where
  one : A → B → A ← B
  one a b x y = (a ≡ x) × (b ≡ y)
  Candidates = Σ A λ a → Σ B λ b → R ∘ one a b ⊆ S
  branch : Candidates → A ← B
  branch (a , b , _) = one a b
  joined = ⋃ branch

  -- Every admitted singleton is safe to compose with R. The two
  -- endpoint equalities let us use its certificate on this very edge.
  cancel : R ∘ joined ⊆ S
  cancel (x , r , (a , b , safe) , eq) = safe (x , r , eq)

  -- Given an edge x of an admissible X, its singleton is admissible:
  -- replace the singleton test by x inside the original composition.
  introduce : (X : A ← B) → R ∘ X ⊆ S → X ⊆ joined
  introduce X law {b = a} {a = b} x = (a , b , safe) , refl , refl
    where safe : R ∘ one a b ⊆ S
          safe (_ , r , refl , refl) = law (_ , r , x)

  into : joined ⊆ R ＼ S
  into {b = a} j r = cancel (a , r , j)
  out : R ＼ S ⊆ joined
  out = introduce (R ＼ S) (λ { (_ , r , all) → all r })
