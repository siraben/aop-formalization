{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.Snoc where

open import AoP.Common.Prelude
private variable A B : Set

-- §1.3. The outermost constructor holds the *last* element.
infixl 5 _▻_
data Snoc (A : Set) : Set where
  ε : Snoc A
  _▻_ : Snoc A → A → Snoc A

foldl : B → (B → A → B) → Snoc A → B
foldl z s ε = z
foldl z s (xs ▻ x) = s (foldl z s xs) x

infixr 6 _++_
_++_ : Snoc A → Snoc A → Snoc A
xs ++ ys = foldl xs _▻_ ys

unitˡ : (xs : Snoc A) → ε ++ xs ≡ xs
unitˡ ε = refl
unitˡ (xs ▻ x) = cong (_▻ x) (unitˡ xs)

assoc : (xs ys zs : Snoc A) → xs ++ (ys ++ zs) ≡ (xs ++ ys) ++ zs
assoc xs ys ε = refl
assoc xs ys (zs ▻ z) = begin
  xs ++ (ys ++ (zs ▻ z))
    ≡⟨⟩  -- unfold concatenation twice
  (xs ++ (ys ++ zs)) ▻ z
    ≡⟨ cong (_▻ z) (assoc xs ys zs) ⟩  -- induction on the final list
  ((xs ++ ys) ++ zs) ▻ z
    ≡⟨⟩  -- fold concatenation back up
  (xs ++ ys) ++ (zs ▻ z) ∎

-- Carry the already converted suffix instead of repeatedly appending at
-- the end of a cons-list. Both conversions visit each constructor once.
prepend : Snoc A → List A → List A
prepend ε ys = ys
prepend (xs ▻ x) ys = prepend xs (x ∷ ys)

append : Snoc A → List A → Snoc A
append xs [] = xs
append xs (y ∷ ys) = append (xs ▻ y) ys

fromSnoc : Snoc A → List A
fromSnoc xs = prepend xs []

toSnoc : List A → Snoc A
toSnoc = append ε

-- These stronger accumulator laws yield both inverse laws at empty suffix.
append-prepend : (xs : Snoc A) (ys : List A) → toSnoc (prepend xs ys) ≡ append xs ys
append-prepend ε ys = refl
append-prepend (xs ▻ x) ys = append-prepend xs (x ∷ ys)

prepend-append : (xs : Snoc A) (ys zs : List A) →
                 prepend (append xs ys) zs ≡ prepend xs (prepend (toSnoc ys) zs)
prepend-append xs [] zs = refl
prepend-append xs (y ∷ ys) zs = prepend-append (xs ▻ y) ys zs ∙
  cong (prepend xs) (sym (prepend-append (ε ▻ y) ys zs))
  where
  sym : ∀ {T : Set} {a b : T} → a ≡ b → b ≡ a
  sym refl = refl

snoc-round-trip : (xs : Snoc A) → toSnoc (fromSnoc xs) ≡ xs
snoc-round-trip xs = append-prepend xs []

cons-round-trip : (ys : List A) → fromSnoc (toSnoc ys) ≡ ys
cons-round-trip [] = refl
cons-round-trip (y ∷ ys) = prepend-append (ε ▻ y) ys [] ∙ cong (y ∷_) (cons-round-trip ys)
