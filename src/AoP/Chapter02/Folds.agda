{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.Folds where

open import AoP.Common.Prelude
private variable A B C : Set

-- Agda reserves ⦇ ⦈ for idiom brackets; use white parentheses instead.
⦅_∣_⦆ : B → (A → B → B) → List A → B
⦅ e ∣ f ⦆ []       = e
⦅ e ∣ f ⦆ (x ∷ xs) = f x (⦅ e ∣ f ⦆ xs)

unique : (h : List A → B) (e : B) (f : A → B → B) → h [] ≡ e →
         (∀ x xs → h (x ∷ xs) ≡ f x (h xs)) → ∀ xs → h xs ≡ ⦅ e ∣ f ⦆ xs
unique h e f nil step [] = nil
unique h e f nil step (x ∷ xs) = begin
  h (x ∷ xs)           ≡⟨ step x xs ⟩
  f x (h xs)           ≡⟨ cong (f x) (unique h e f nil step xs) ⟩
  f x (⦅ e ∣ f ⦆ xs)   ≡⟨⟩
  ⦅ e ∣ f ⦆ (x ∷ xs)   ∎

fusion : (h : B → C) (e : B) (f : A → B → B) (g : A → C → C) →
         (∀ x b → h (f x b) ≡ g x (h b)) →
         ∀ xs → h (⦅ e ∣ f ⦆ xs) ≡ ⦅ h e ∣ g ⦆ xs
-- To fuse the consumer h into the fold, derive the constructor
-- equations for their composite. The empty case gives the seed h e;
-- pushing h past f in the cons case identifies the new update g.
fusion h e f g law = unique (λ xs → h (⦅ e ∣ f ⦆ xs)) (h e) g refl λ x xs → begin
  h (⦅ e ∣ f ⦆ (x ∷ xs))   ≡⟨⟩
  h (f x (⦅ e ∣ f ⦆ xs))   ≡⟨ law x (⦅ e ∣ f ⦆ xs) ⟩
  g x (h (⦅ e ∣ f ⦆ xs))   ∎

banana-split : (e : B) (f : A → B → B) (d : C) (g : A → C → C) →
               ∀ xs → (⦅ e ∣ f ⦆ xs , ⦅ d ∣ g ⦆ xs) ≡
                      ⦅ (e , d) ∣ (λ x p → f x (fst p) , g x (snd p)) ⦆ xs
banana-split e f d g = unique both (e , d) update refl λ x xs → begin
  both (x ∷ xs)                            ≡⟨⟩  -- unfold both folds at cons
  (f x (⦅ e ∣ f ⦆ xs) , g x (⦅ d ∣ g ⦆ xs)) ≡⟨⟩  -- use the two fields of the tail result
  update x (both xs)                       ∎
  where both = λ xs → ⦅ e ∣ f ⦆ xs , ⦅ d ∣ g ⦆ xs
        update = λ x p → f x (fst p) , g x (snd p)
