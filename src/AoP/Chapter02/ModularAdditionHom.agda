{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ModularAdditionHom where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; suc; zero; _+_)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter06.BinaryModulus using (module Compute)
open import AoP.Chapter02.RemainderUnique using (module Law)

-- §2.6. The square functor maps both operands before addition. Show
-- that reducing their sum directly gives exactly the same residue.
module Mod (k : Nat) where
  open Compute k
  b = suc k
  Residue = Σ Nat (λ n → n ≤ k)
  reduce : Nat → Residue
  reduce n = fst (solve n) , fst (snd (solve n))
  plus : Residue × Residue → Residue
  plus (x , y) = reduce (fst x + fst y)
  rem : Nat → Nat
  rem n = fst (reduce n)
  private
    assoc : ∀ a c d → (a + c) + d ≡ a + (c + d)
    assoc zero c d = refl
    assoc (suc a) c d = cong suc (assoc a c d)
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
    slide : ∀ a n → a + suc n ≡ suc (a + n)
    slide zero n = refl
    slide (suc a) n = cong suc (slide a n)
    unit : ∀ n → n + 0 ≡ n
    unit zero = refl
    unit (suc n) = cong suc (unit n)
    comm : ∀ a n → a + n ≡ n + a
    comm zero n = rev (unit n)
    comm (suc a) n = cong suc (comm a n) ∙ rev (slide n a)
    strip : ∀ {r n} → Copies r n → ∀ y → rem (n + y) ≡ rem (r + y)
    strip same y = refl
    strip (add {n} p) y = cong rem (assoc b n y) ∙ Law.periodic k (n + y) ∙ strip p y
    -- The natural representative determines its bound proof as well.
    bounds : ∀ {n t} (u v : n ≤ t) → u ≡ v
    bounds z≤ z≤ = refl
    bounds (s≤ u) (s≤ v) = cong s≤ (bounds u v)
    agree : ∀ (x y : Residue) → fst x ≡ fst y → x ≡ y
    agree (x , u) (.x , v) refl = cong (x ,_) (bounds u v)
  hom : ∀ x y → reduce (x + y) ≡ plus (reduce x , reduce y)
  hom x y = agree _ _ (begin
    rem (x + y) ≡⟨ strip (snd (snd (solve x))) y ⟩
    rem (rem x + y) ≡⟨ cong rem (comm (rem x) y) ⟩
    rem (y + rem x) ≡⟨ strip (snd (snd (solve y))) (rem x) ⟩
    rem (rem y + rem x) ≡⟨ cong rem (comm (rem y) (rem x)) ⟩
    rem (rem x + rem y) ∎)

-- Modulo five, the inputs 8 and 9 become 3 and 4; their sum 7 wraps
-- to 2, also the remainder of the original sum 17.
example : Mod.rem 4 (8 + 9) ≡ 2
example = begin
  Mod.rem 4 (8 + 9) ≡⟨ cong fst (Mod.hom 4 8 9) ⟩
  Mod.rem 4 (Mod.rem 4 8 + Mod.rem 4 9) ≡⟨⟩
  Mod.rem 4 (3 + 4) ≡⟨⟩
  Mod.rem 4 7 ≡⟨⟩
  2 ∎
