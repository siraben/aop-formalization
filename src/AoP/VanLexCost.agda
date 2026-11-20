{-# OPTIONS --safe --without-K #-}
module AoP.VanLexCost where

open import AoP.Prelude
open import AoP.Paragraph using (Nonempty; _∷⁺_)
open import AoP.NatOrder using (_≤_; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.57, additive natural costs. For the printed order the
-- chosen partition is all singletons. Testing one feasible block at
-- a time suffices to tell whether that partition also minimizes cost.
module Criterion {A : Set} (ok : Nonempty A → Set) (cost : Nonempty A → Nat) where
  units : List A → Nat
  units [] = 0
  units (a ∷ as) = cost (a ∷⁺ []) + units as
  broken : Nonempty A → Nat
  broken (a ∷⁺ as) = units (a ∷ as)
  total : (Nonempty A → Nat) → List (Nonempty A) → Nat
  total f [] = 0
  total f (b ∷ bs) = f b + total f bs
  data Valid : List (Nonempty A) → Set where
    end : Valid []
    add : ∀ {b bs} → ok b → Valid bs → Valid (b ∷ bs)

  Local = ∀ b → ok b → broken b ≤ cost b
  Global = ∀ bs → Valid bs → total broken bs ≤ total cost bs
  sufficient : Local → Global
  sufficient local [] end = rid 0
  sufficient local (b ∷ bs) (add pass rest) = sum-mono (local b pass) (sufficient local bs rest)
  private
    unit : ∀ x → x + 0 ≡ x
    unit 0 = refl
    unit (suc x) = cong suc (unit x)
  necessary : Global → Local
  necessary global b pass with global (b ∷ []) (add pass end)
  ... | le rewrite unit (broken b) | unit (cost b) = le
