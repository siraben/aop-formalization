{-# OPTIONS --safe --without-K #-}
module AoP.Inverses where

open import AoP.Prelude
open import AoP.Folds
private variable A B : Set

-- §1.5. The forked output of unzip is computed by a single fold.
unzip : List (A × B) → List A × List B
unzip = ⦅ ([] , []) ∣ (λ { (a , b) (as , bs) → (a ∷ as) , (b ∷ bs) }) ⦆

-- Exercise 1.15: the carrier of the fold is a *function* awaiting the
-- second list. On unequal lengths the total extension truncates.
zip : List A → List B → List (A × B)
zip = ⦅ (λ _ → []) ∣ step ⦆
  where
  step : A → (List B → List (A × B)) → List B → List (A × B)
  step a k [] = []
  step a k (b ∷ bs) = (a , b) ∷ k bs

zipPair : List A × List B → List (A × B)
zipPair (as , bs) = zip as bs

-- The inverse specification holds on the image of unzip. It does *not*
-- require zip to recover the unused suffix of an arbitrary pair of lists.
zip-unzip : (ps : List (A × B)) → zipPair (unzip ps) ≡ ps
zip-unzip [] = refl
zip-unzip ((a , b) ∷ ps) = begin
  zipPair (unzip ((a , b) ∷ ps))
    ≡⟨⟩  -- unfold both cons cases
  (a , b) ∷ zipPair (unzip ps)
    ≡⟨ cong ((a , b) ∷_) (zip-unzip ps) ⟩
  (a , b) ∷ ps ∎

-- Equal-length inputs are the precise domain for the opposite direction.
data Aligned {A B : Set} : List A → List B → Set where
  empty : Aligned [] []
  next : ∀ {a b as bs} → Aligned as bs → Aligned (a ∷ as) (b ∷ bs)

unzip-zip : ∀ {as : List A} {bs : List B} → Aligned as bs → unzip (zip as bs) ≡ (as , bs)
unzip-zip empty = refl
unzip-zip (next {a} {b} {as} {bs} p) = begin
  unzip (zip (a ∷ as) (b ∷ bs))
    ≡⟨ cong extend (unzip-zip p) ⟩  -- strip matching heads, then use induction
  (a ∷ as) , (b ∷ bs) ∎
  where extend = λ pair → (a ∷ fst pair) , (b ∷ snd pair)
