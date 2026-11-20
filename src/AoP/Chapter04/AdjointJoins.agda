{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.AdjointJoins where

open import AoP.Common.Prelude

-- Exercise 4.40. To invert an inequality f x ≤ y, join all inputs
-- whose images lie below y. Preservation of joins makes the resulting
-- input admissible too. In the other direction the adjunction itself
-- proves that f carries a least upper bound to a least upper bound.
record Joins (A : Set) : Set₁ where
  field
    _≤_ : A → A → Set
    refl≤ : ∀ x → x ≤ x
    trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
    antisym : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
    sup : ∀ {I : Set} → (I → A) → A
    member : ∀ {I : Set} (v : I → A) i → v i ≤ sup v
    least : ∀ {I : Set} (v : I → A) z → (∀ i → v i ≤ z) → sup v ≤ z

module Rule {A B : Set} (a : Joins A) (b : Joins B) (f : A → B) (g : B → A)
            (mono : ∀ {x y} → Joins._≤_ a x y → Joins._≤_ b (f x) (f y)) where
  private module A = Joins a
  private module B = Joins b
  Lower : B → Set
  Lower y = Σ _ λ x → f x B.≤ y
  best : B → A
  best y = A.sup (fst {B = λ x → f x B.≤ y})
  Connection = ∀ x y → ((f x B.≤ y) → (x A.≤ g y)) × ((x A.≤ g y) → (f x B.≤ y))
  Preserves = ∀ {I : Set} (v : I → A) → f (A.sup v) ≡ B.sup (λ i → f (v i))

  preserves : Connection → Preserves
  preserves adj v = B.antisym
    (snd (adj _ _) (A.least v _ (λ i → fst (adj _ _) (B.member _ i))))
    (B.least _ _ (λ i → mono (A.member v i)))

  formula : Connection → ∀ y → g y ≡ best y
  formula adj y = A.antisym (A.member _ (g y , snd (adj _ _) (A.refl≤ _)))
    (A.least _ _ (λ { (x , p) → fst (adj x y) p }))

  recover : Preserves → (∀ y → g y ≡ best y) → Connection
  recover pres eq x y rewrite eq y = (λ p → A.member _ (x , p)) , unbound
    where
    candidates : Lower y → A
    candidates = fst
    feasible : f (best y) B.≤ y
    feasible rewrite pres candidates = B.least _ y snd
    unbound : x A.≤ best y → f x B.≤ y
    unbound p = B.trans (mono p) feasible
