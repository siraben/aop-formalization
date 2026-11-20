{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.EditScript where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter03.Horner using (map)

-- §9.2 — Describe an edit without being given either string. A copy
-- contributes a letter to both strings; a deletion only to the source;
-- an insertion only to the target. Thus [copy A, delete B, insert C]
-- encodes AB → AC. Scripts are not unique: deleting A then inserting A
-- has the same effect as copying A, but costs two operations, not one.
-- The optimization problem is to find a shortest script decoding to a
-- given pair. Here we formalize feasibility and the source/target symmetry.
data Op (A : Set) : Set where
  copy delete insert : A → Op A

module Scripts {A : Set} where
  Strings = List A × List A

  step : Op A → Strings → Strings
  step (copy a)   (xs , ys) = (a ∷ xs) , (a ∷ ys)
  step (delete a) (xs , ys) = (a ∷ xs) , ys
  step (insert a) (xs , ys) = xs , (a ∷ ys)

  edit : List (Op A) → Strings
  edit = ⦅ ([] , []) ∣ step ⦆

  flip : Op A → Op A
  flip (copy a) = copy a
  flip (delete a) = insert a
  flip (insert a) = delete a

  swap : Strings → Strings
  swap (xs , ys) = ys , xs

  commute : ∀ o p → swap (step o p) ≡ step (flip o) (swap p)
  commute (copy _) _ = refl
  commute (delete _) _ = refl
  commute (insert _) _ = refl

  symmetry : ∀ ops → swap (edit ops) ≡ edit (map flip ops)
  symmetry [] = refl
  symmetry (o ∷ ops) = begin
    swap (step o (edit ops))       ≡⟨ commute o (edit ops) ⟩
    step (flip o) (swap (edit ops)) ≡⟨ cong (step (flip o)) (symmetry ops) ⟩
    edit (map flip (o ∷ ops)) ∎

  -- A witness indexed by endpoints can only describe a feasible script.
  data Script : List A → List A → Set where
    done : Script [] []
    cpy : ∀ {x xs ys} → Script xs ys → Script (x ∷ xs) (x ∷ ys)
    del : ∀ {x xs ys} → Script xs ys → Script (x ∷ xs) ys
    ins : ∀ {x xs ys} → Script xs ys → Script xs (x ∷ ys)

  erase : ∀ {xs ys} → Script xs ys → List (Op A)
  erase done = []
  erase (cpy {x} p) = copy x ∷ erase p
  erase (del {x} p) = delete x ∷ erase p
  erase (ins {x} p) = insert x ∷ erase p

  feasible : ∀ {xs ys} (s : Script xs ys) → edit (erase s) ≡ (xs , ys)
  feasible done = refl
  feasible (cpy {x} s) = cong (step (copy x)) (feasible s)
  feasible (del {x} s) = cong (step (delete x)) (feasible s)
  feasible (ins {x} s) = cong (step (insert x)) (feasible s)

  decode : ∀ ops → Script (fst (edit ops)) (snd (edit ops))
  decode [] = done
  decode (copy x ∷ ops) = cpy (decode ops)
  decode (delete x ∷ ops) = del (decode ops)
  decode (insert x ∷ ops) = ins (decode ops)
