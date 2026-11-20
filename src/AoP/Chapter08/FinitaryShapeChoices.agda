{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.FinitaryShapeChoices where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image; preimage)
open import AoP.Chapter05.CartesianMenuPairs using (module Menus)
open import AoP.Chapter03.Horner using (map)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Exercise 8.20. Shapes may range over an infinite type, and their
-- arities may be unbounded. Only the arity of the *input* shape matters:
-- its n slots can be traversed, even though listing every shape cannot.
Slots : Nat → Set → Set
Slots zero A = ⊤
Slots (suc n) A = A × Slots n A

module Choices {A : Set} where
  pool : ∀ n → Slots n (List A) → List (Slots n A)
  pool zero _ = tt ∷ []
  pool (suc n) (xs , ms) = Menus.cpp xs (pool n ms)
  Good : ∀ n → Slots n (List A) → Slots n A → Set
  Good zero _ _ = ⊤
  Good (suc n) (xs , ms) (a , as) = (a ∈ xs) × Good n ms as

  sound : ∀ n ms v → v ∈ pool n ms → Good n ms v
  sound zero _ _ _ = tt
  sound (suc n) (xs , ms) (a , as) mem with fst (Menus.pairs xs (pool n ms)) (a , as) mem
  ... | h , t = h , sound n ms as t
  complete : ∀ n ms v → Good n ms v → v ∈ pool n ms
  complete zero _ tt _ = here
  complete (suc n) (xs , ms) (a , as) (h , t) = snd (Menus.pairs xs (pool n ms)) (a , as) (h , complete n ms as t)

module Container (Shape : Set) (arity : Shape → Nat) where
  T : Set → Set
  T A = Σ Shape (λ s → Slots (arity s) A)
  listcp : ∀ {A} → T (List A) → List (T A)
  listcp (s , ms) = map (s ,_) (Choices.pool (arity s) ms)
  -- State validity with an explicit shape-preservation witness. This
  -- avoids both decidable shape equality and uniqueness of its proofs.
  Valid : ∀ {A} → T (List A) → T A → Set
  Valid (s , ms) y = Σ _ λ v → Choices.Good (arity s) ms v × ((s , v) ≡ y)
  sound : ∀ {A} (x : T (List A)) y → y ∈ listcp x → Valid x y
  sound (s , ms) y p with preimage (s ,_) (Choices.pool (arity s) ms) p
  ... | v , mem , eq = v , Choices.sound (arity s) ms v mem , eq
  complete : ∀ {A} (x : T (List A)) y → Valid x y → y ∈ listcp x
  complete (s , ms) .(s , v) (v , good , refl) = image (s ,_) (Choices.complete (arity s) ms v good)

-- Use the arity itself as the shape. No global upper bound exists.
-- The nullary shape needs no choices, whereas a missing option at a
-- required slot makes the whole unary pool empty.
module Example where
  open Container Nat (λ n → n)
  nullary : listcp {Nat} (0 , tt) ≡ (0 , tt) ∷ []
  nullary = refl
  missing : listcp {Nat} (1 , [] , tt) ≡ []
  missing = refl
  binary : listcp {Nat} (2 , (1 ∷ 2 ∷ []) , (7 ∷ []) , tt) ≡
    (2 , 1 , 7 , tt) ∷ (2 , 2 , 7 , tt) ∷ []
  binary = refl
