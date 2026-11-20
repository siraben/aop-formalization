{-# OPTIONS --safe --without-K #-}
module AoP.ZipInverseDomain where

open import AoP.Prelude
open import AoP.Inverses using (zip; unzip; Aligned; empty; next; unzip-zip)
open import Agda.Builtin.Nat using (Nat)

-- §1.5. To recover both inputs after zipping, neither input may have an
-- unused tail. Every unzip produces aligned lists, so this condition is
-- necessary as well as sufficient for the truncating extension of zip.
aligned-image : ∀ {A B} (ps : List (A × B)) → Aligned (fst (unzip ps)) (snd (unzip ps))
aligned-image [] = empty
aligned-image ((a , b) ∷ ps) = next (aligned-image ps)

necessary : ∀ {A B} (as : List A) (bs : List B) → unzip (zip as bs) ≡ (as , bs) → Aligned as bs
necessary {A} {B} as bs eq = transport eq (aligned-image (zip as bs))
  where transport : ∀ {p q : List A × List B} → p ≡ q → Aligned (fst p) (snd p) → Aligned (fst q) (snd q)
        transport refl ok = ok

-- With one excess input the intermediate singleton has no place to
-- store 2. Unzipping can therefore recover only the first left entry.
loss : unzip (zip (1 ∷ 2 ∷ []) (3 ∷ [])) ≡ ((1 ∷ []) , (3 ∷ []))
loss = begin
  unzip (zip (1 ∷ 2 ∷ []) (3 ∷ [])) ≡⟨⟩
  unzip ((1 , 3) ∷ zip (2 ∷ []) []) ≡⟨⟩
  unzip ((1 , 3) ∷ []) ≡⟨⟩
  ((1 ∷ []) , (3 ∷ [])) ∎
