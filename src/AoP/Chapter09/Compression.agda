{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.Compression where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)

-- §9.4. A literal adds one letter. A pointer (offset,length) copies
-- letters from earlier in the growing output, using a zero-based absolute
-- offset. It may overlap its destination: after a single A, copying three
-- letters starting at zero produces AAAA, not an out-of-bounds error.
-- Optimization asks for a cheapest program decoding to the desired text;
-- here we define decoding, including failure, and prove feasibility.
module Text {A : Set} where
  data Code : Set where
    sym : A → Code
    ptr : Nat → Nat → Code  -- second argument stores length minus one

  lookup : Nat → List A → Maybe A
  lookup _ [] = nothing
  lookup zero (x ∷ xs) = just x
  lookup (suc i) (_ ∷ xs) = lookup i xs

  copy : Nat → Nat → List A → Maybe (List A)
  copy i zero xs = just xs
  copy i (suc k) xs with lookup i xs
  ... | nothing = nothing
  ... | just x = copy (suc i) k (xs ++ (x ∷ []))

  run : List A → List Code → Maybe (List A)
  run xs [] = just xs
  run xs (sym a ∷ ops) = run (xs ++ (a ∷ [])) ops
  run xs (ptr i k ∷ ops) with copy i (suc k) xs
  ... | nothing = nothing
  ... | just ys = run ys ops

  -- Every text has an encoding even if no pointers save space. The
  -- stronger prefix law explains why the induction hypothesis applies
  -- after emitting a literal rather than only at the start of a stream.
  literals : List A → List Code
  literals [] = []
  literals (x ∷ xs) = sym x ∷ literals xs

  assoc : ∀ (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)

  prefix-law : ∀ xs ys → run xs (literals ys) ≡ just (xs ++ ys)
  prefix-law [] [] = refl
  prefix-law (x ∷ xs) [] = cong just (unit (x ∷ xs))
    where
    unit : (zs : List A) → zs ≡ zs ++ []
    unit [] = refl
    unit (z ∷ zs) = cong (z ∷_) (unit zs)
  prefix-law xs (y ∷ ys) = begin
    run (xs ++ (y ∷ [])) (literals ys) ≡⟨ prefix-law (xs ++ (y ∷ [])) ys ⟩
    just ((xs ++ (y ∷ [])) ++ ys)     ≡⟨ cong just (assoc xs (y ∷ []) ys) ⟩
    just (xs ++ (y ∷ ys)) ∎

  round-trip : ∀ xs → run [] (literals xs) ≡ just xs
  round-trip = prefix-law []

  overlapping-copy : ∀ a → run [] (sym a ∷ ptr 0 2 ∷ []) ≡ just (a ∷ a ∷ a ∷ a ∷ [])
  overlapping-copy a = refl
  bad-start : ∀ i k → run [] (ptr i k ∷ []) ≡ nothing
  bad-start i k = refl
