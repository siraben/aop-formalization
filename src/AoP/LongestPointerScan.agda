{-# OPTIONS --safe --without-K #-}
module AoP.LongestPointerScan where

open import AoP.Prelude
open import AoP.DictionaryTable using (module Table)
open import AoP.DictionarySearch using (module Encode)
open import AoP.Compression using (module Text)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid; compare; chain)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

-- Search earlier rows and bounded tokens for the longest pointer that
-- ends exactly at this prefix. A pointer's stored span is length minus
-- one, so maximizing it also maximizes the number of copied letters.
module Scan {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) (ys : List A) where
  open Text {A}
  open Table eq? target c p using (Row; reaches?)
  open Encode eq? target using (tokens)
  record Hit : Set where
    constructor hit
    field row : Row
          offset span : Nat
          legal : run (fst row) (ptr offset span ∷ []) ≡ just ys
  open Hit
  data Max (P : Hit → Set) : Set where
    none : (∀ h → P h → ⊥) → Max P
    won : (h : Hit) → P h → (∀ t → P t → span t ≤ span h) → Max P
  module _ {P Q : Hit → Set} where
    merge : Max P → Max Q → Max (λ h → P h ⊎ Q h)
    merge (none l) (none r) = none λ { t (inl x) → l t x ; t (inr y) → r t y }
    merge (won h x le) (none r) = won h (inl x) λ { t (inl z) → le t z ; t (inr z) → absurd (r t z) }
      where absurd : ∀ {X : Set} → ⊥ → X
            absurd ()
    merge (none l) (won h y le) = won h (inr y) λ { t (inl z) → absurd (l t z) ; t (inr z) → le t z }
      where absurd : ∀ {X : Set} → ⊥ → X
            absurd ()
    merge (won h x l) (won t y r) with compare (span h) (span t)
    ... | inl le = won t (inr y) λ { u (inl z) → chain (l u z) le ; u (inr z) → r u z }
    ... | inr le = won h (inl x) λ { u (inl z) → l u z ; u (inr z) → chain (r u z) le }
  convert : ∀ {P Q} → (∀ h → P h → Q h) → (∀ h → Q h → P h) → Max P → Max Q
  convert f g (none no) = none λ h z → no h (g h z)
  convert f g (won h z le) = won h (f h z) λ t q → le t (g t q)
  token = λ h → ptr (offset h) (span h)
  At : Row → Code → Hit → Set
  At r op h = (row h ≡ r) × (token h ≡ op)
  test : ∀ r op → Max (At r op)
  test r (sym a) = none λ { h (_ , ()) }
  test r (ptr i k) with reaches? (fst r) (ptr i k) ys
  ... | inr no = none λ { h (refl , refl) → no (legal h) }
  ... | inl yes = won (hit r i k yes) (refl , refl) λ { h (_ , refl) → rid _ }
  Member : ∀ {B : Set} {x b : B} {bs} → x ∈ b ∷ bs → (x ≡ b) ⊎ (x ∈ bs)
  Member here = inl refl
  Member (there m) = inr m
  first : ∀ {B : Set} {x b : B} {bs} → x ≡ b → x ∈ b ∷ bs
  first refl = here
  scan : ∀ r ops → Max (λ h → (row h ≡ r) × (token h ∈ ops))
  scan r [] = none λ { h (_ , ()) }
  scan r (op ∷ ops) = convert {P = λ h → At r op h ⊎ ((row h ≡ r) × (token h ∈ ops))} (λ { h (inl (eq , e)) → eq , first e ; h (inr (eq , m)) → eq , there m })
    (λ { h (eq , m) → distribute {h} eq (Member m) }) (merge (test r op) (scan r ops))
    where distribute : ∀ {h} → row h ≡ r → (token h ≡ op) ⊎ (token h ∈ ops) → At r op h ⊎ ((row h ≡ r) × (token h ∈ ops))
          distribute eq (inl p) = inl (eq , p)
          distribute eq (inr m) = inr (eq , m)
  longest : ∀ rs → Max (λ h → (row h ∈ rs) × (token h ∈ tokens))
  longest [] = none λ { h (() , _) }
  longest (r ∷ rs) = convert {P = λ h → ((row h ≡ r) × (token h ∈ tokens)) ⊎ ((row h ∈ rs) × (token h ∈ tokens))} (λ { h (inl (e , m)) → first e , m ; h (inr (n , m)) → there n , m })
    (λ { h (here , m) → inl (refl , m) ; h (there n , m) → inr (n , m) }) (merge (scan r tokens) (longest rs))
