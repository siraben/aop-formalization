{-# OPTIONS --safe --without-K #-}
module AoP.Folds where

open import AoP.Prelude
private variable A B C : Set

-- Agda reserves ⦇ ⦈ for idiom brackets; use white parentheses instead.
⦅_∣_⦆ : B → (A → B → B) → List A → B
⦅ e ∣ f ⦆ []       = e
⦅ e ∣ f ⦆ (x ∷ xs) = f x (⦅ e ∣ f ⦆ xs)

unique : (h : List A → B) (e : B) (f : A → B → B) → h [] ≡ e →
         (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) → ∀ xs → h xs ≡ ⦅ e ∣ f ⦆ xs
unique h e f nil step [] = nil
unique h e f nil step (x ∷ xs) = step x xs ∙ cong (f x) (unique h e f nil step xs)

fusion : (h : B → C) (e : B) (f : A → B → B) (g : A → C → C) →
         (∀ x b → h (f x b) ≡ g x (h b)) →
         ∀ xs → h (⦅ e ∣ f ⦆ xs) ≡ ⦅ h e ∣ g ⦆ xs
fusion h e f g law = unique (λ xs → h (⦅ e ∣ f ⦆ xs)) (h e) g refl
                            (λ x xs → law x (⦅ e ∣ f ⦆ xs))

banana-split : (e : B) (f : A → B → B) (d : C) (g : A → C → C) →
               ∀ xs → (⦅ e ∣ f ⦆ xs , ⦅ d ∣ g ⦆ xs) ≡
                      ⦅ (e , d) ∣ (λ x p → f x (fst p) , g x (snd p)) ⦆ xs
banana-split e f d g = unique (λ xs → ⦅ e ∣ f ⦆ xs , ⦅ d ∣ g ⦆ xs)
                             (e , d) _ refl (λ x xs → refl)
