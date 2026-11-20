{-# OPTIONS --safe --without-K #-}
module AoP.ImageComparison where

open import AoP.Prelude

-- Exercise 4.20, uniqueness in Fun. Suppose two tables of image
-- values represent the same function. To translate a first-table entry,
-- choose any input reaching it and take the second table's entry for
-- that input. Injectivity of the output column forces this translation.
module Compare {A B I J : Set} (c : A → I) (m : I → B) (d : A → J) (n : J → B)
               (same : ∀ a → m (c a) ≡ n (d a))
               (onto-c : ∀ i → Σ A (λ a → c a ≡ i)) (onto-d : ∀ j → Σ A (λ a → d a ≡ j))
               (inj-m : ∀ {x y} → m x ≡ m y → x ≡ y) (inj-n : ∀ {x y} → n x ≡ n y → x ≡ y) where
  private
    back : ∀ {T : Set} {x y : T} → x ≡ y → y ≡ x
    back refl = refl

  to : I → J
  to i = d (fst (onto-c i))
  from : J → I
  from j = c (fst (onto-d j))

  output : ∀ i → n (to i) ≡ m i
  output i with onto-c i
  ... | a , refl = back (same a)
  output′ : ∀ j → m (from j) ≡ n j
  output′ j with onto-d j
  ... | a , refl = same a

  input : ∀ a → to (c a) ≡ d a
  input a = inj-n (output (c a) ∙ same a)
  inverseˡ : ∀ i → from (to i) ≡ i
  inverseˡ i = inj-m (output′ (to i) ∙ output i)
  inverseʳ : ∀ j → to (from j) ≡ j
  inverseʳ j = inj-n (output (from j) ∙ output′ j)
  unique : (k : I → J) → (∀ i → n (k i) ≡ m i) → ∀ i → k i ≡ to i
  unique k respects i = inj-n (respects i ∙ back (output i))
