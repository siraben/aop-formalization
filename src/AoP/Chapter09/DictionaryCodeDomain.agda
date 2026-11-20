{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryCodeDomain where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import Agda.Builtin.Nat using (suc)
open import Agda.Builtin.Maybe using (just; nothing)
open import AoP.Chapter01.Naturality using (_++_)

-- Exercise 9.20, domain for absolute-offset pointers. A first literal
-- supplies a source for offset zero; it cannot validate all offsets.
module Domain {A : Set} where
  open Text {A}
  first-literal-fails : ∀ a → run [] (sym a ∷ ptr 1 0 ∷ []) ≡ nothing
  first-literal-fails a = refl

  -- At each instruction carry exactly the state required by the next
  -- instruction. This retains every successful raw instruction list.
  data Program (xs : List A) : Set where
    halt : Program xs
    emit : ∀ a → Program (xs ++ (a ∷ [])) → Program xs
    repeat-from : ∀ i k {ys} → copy i (suc k) xs ≡ just ys → Program ys → Program xs
  decode : ∀ {xs} → Program xs → List A
  decode {xs} halt = xs
  decode (emit _ q) = decode q
  decode (repeat-from _ _ _ q) = decode q
  erase : ∀ {xs} → Program xs → List Code
  erase halt = []
  erase (emit a q) = sym a ∷ erase q
  erase (repeat-from i k _ q) = ptr i k ∷ erase q
  sound : ∀ {xs} (q : Program xs) → run xs (erase q) ≡ just (decode q)
  sound halt = refl
  sound (emit a q) = sound q
  sound (repeat-from i k ok q) rewrite ok = sound q
  complete : ∀ xs ops {ys} → run xs ops ≡ just ys → Σ (Program xs) λ q → (erase q ≡ ops) × (decode q ≡ ys)
  complete xs [] refl = halt , refl , refl
  complete xs (sym a ∷ ops) ok with complete (xs ++ (a ∷ [])) ops ok
  ... | q , refl , refl = emit a q , refl , refl
  complete xs (ptr i k ∷ ops) ok with copy i (suc k) xs in step
  ... | nothing with ok
  ...   | ()
  complete xs (ptr i k ∷ ops) ok | just zs with complete zs ops ok
  ... | q , refl , refl = repeat-from i k step q , refl , refl
  onto : ∀ ys → Σ (Program []) λ q → decode q ≡ ys
  onto ys with complete [] (literals ys) (round-trip ys)
  ... | q , _ , eq = q , eq
