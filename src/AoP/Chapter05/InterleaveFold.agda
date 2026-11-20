{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.InterleaveFold where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat)
open import AoP.Chapter04.Relations using (Fold; nil; cons; _˘)
private variable A : Set

-- Exercise 5.29. To recognize a merge of two lists, read its output
-- and assign every entry to one of two source lists, in order. Folding
-- the output from the right, prepend each entry to either partial list.
-- The converse of that splitting relation generates interleavings.
data Assign {A : Set} (x : A) : List A × List A → List A × List A → Set where
  left : ∀ {ys zs} → Assign x (x ∷ ys , zs) (ys , zs)
  right : ∀ {ys zs} → Assign x (ys , x ∷ zs) (ys , zs)

Split : List A × List A → List A → Set
Split = Fold (_≡ ([] , [])) (λ out p → Assign (fst p) out (snd p))

-- Independent specification: at each step consume the head of one
-- of the two inputs. When both are empty, the only result is empty.
data Merge {A : Set} : List A → List A → List A → Set where
  end : Merge [] [] []
  takeˡ : ∀ {a ys zs xs} → Merge ys zs xs → Merge (a ∷ ys) zs (a ∷ xs)
  takeʳ : ∀ {a ys zs xs} → Merge ys zs xs → Merge ys (a ∷ zs) (a ∷ xs)

sound : ∀ {xs ys zs : List A} → (Split ˘) xs (ys , zs) → Merge ys zs xs
sound (nil refl) = end
sound (cons left p) = takeˡ (sound p)
sound (cons right p) = takeʳ (sound p)

complete : ∀ {xs ys zs : List A} → Merge ys zs xs → (Split ˘) xs (ys , zs)
complete end = nil refl
complete (takeˡ p) = cons left (complete p)
complete (takeʳ p) = cons right (complete p)

example : (Split ˘) (1 ∷ 10 ∷ 2 ∷ 3 ∷ 11 ∷ 12 ∷ 4 ∷ [])
                    (1 ∷ 2 ∷ 3 ∷ 4 ∷ [] , 10 ∷ 11 ∷ 12 ∷ [])
example = complete (takeˡ (takeʳ (takeˡ (takeˡ (takeʳ (takeʳ (takeˡ end)))))))
