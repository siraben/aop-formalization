{-# OPTIONS --safe --without-K #-}
module AoP.DisjointFibres where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.Power using (_≐_)

-- Exercise 9.5. To invert a tagged copair at c, first test whether
-- c lies in the left range. Disjointness then rules out all witnesses
-- from the other branch. Outside both ranges the right fibre is empty.
module Law {A B C : Set} (V : C ← A) (W : C ← B) where
  Left = λ c → Σ A (V c)
  Right = λ c → Σ B (W c)
  Disjoint = ∀ c → Left c → Right c → ⊥
  restrict : Disjoint → Right ≐ (λ c → Right c × (Left c → ⊥))
  restrict d = (λ c r → r , λ l → d c l r) , (λ c → fst)
  recover : Right ≐ (λ c → Right c × (Left c → ⊥)) → Disjoint
  recover eq c l r = snd (fst eq c r) l

  fibre : C → A ⊎ B → Set
  fibre c (inl a) = V c a
  fibre c (inr b) = W c b

  module Select (d : Disjoint) (test : ∀ c → Left c ⊎ (Left c → ⊥)) where
    branch : C → A ⊎ B → Set
    branch c z with test c | z
    ... | inl _ | inl a = V c a
    ... | inl _ | inr b = ⊥
    ... | inr _ | inl a = ⊥
    ... | inr _ | inr b = W c b

    empty : ∀ {X : Set} → ⊥ → X
    empty ()
    forward : ∀ c z → fibre c z → branch c z
    forward c z with test c | z
    ... | inl l | inl a = λ v → v
    ... | inl l | inr b = λ w → d c l (b , w)
    ... | inr n | inl a = λ v → n (a , v)
    ... | inr n | inr b = λ w → w
    backward : ∀ c z → branch c z → fibre c z
    backward c z with test c | z
    ... | inl l | inl a = λ v → v
    ... | inl l | inr b = empty
    ... | inr n | inl a = empty
    ... | inr n | inr b = λ w → w
    correct : ∀ c → fibre c ≐ branch c
    correct c = forward c , backward c
