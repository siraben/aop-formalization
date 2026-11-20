{-# OPTIONS --safe --without-K #-}
module AoP.Conditions where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Products using ([_,_])
open import Agda.Builtin.Bool
private variable A B C : Set

-- §3.4. Distributing a product over a sum keeps the context x in the
-- chosen branch. This is why a conditional can inspect a test result
-- without losing the argument to which the chosen function is applied.
distr : A × (B ⊎ C) → (A × B) ⊎ (A × C)
distr (x , inl y) = inl (x , y)
distr (x , inr z) = inr (x , z)

undistr : (A × B) ⊎ (A × C) → A × (B ⊎ C)
undistr = [ (λ p → fst p , inl (snd p)) , (λ p → fst p , inr (snd p)) ]

cancel : (p : A × (B ⊎ C)) → undistr (distr p) ≡ p
cancel (x , inl y) = refl
cancel (x , inr z) = refl

reflect : (s : (A × B) ⊎ (A × C)) → distr (undistr s) ≡ s
reflect (inl _) = refl
reflect (inr _) = refl

tag : Bool → ⊤ ⊎ ⊤
tag true = inl tt
tag false = inr tt

choose : (A → Bool) → (A → B) → (A → B) → A → B
choose p f g x = [ (λ u → f (fst u)) , (λ u → g (fst u)) ] (distr (x , tag (p x)))

-- The point-free definition reduces to the expected branch equations.
then-law : (p : A → Bool) (f g : A → B) → ∀ x → p x ≡ true → choose p f g x ≡ f x
then-law p f g x yes rewrite yes = refl

else-law : (p : A → Bool) (f g : A → B) → ∀ x → p x ≡ false → choose p f g x ≡ g x
else-law p f g x no rewrite no = refl

-- (1.10): preprocessing the argument changes the test and both arms.
before : (h : A → B) (p : B → Bool) (f g : B → C) → ∀ x →
         choose p f g (h x) ≡ choose (λ a → p (h a)) (λ a → f (h a)) (λ a → g (h a)) x
before h p f g x with p (h x)
... | true = refl
... | false = refl

-- (1.11): postprocessing acts only on the selected result.
after : (h : B → C) (p : A → Bool) (f g : A → B) → ∀ x →
        h (choose p f g x) ≡ choose p (λ a → h (f a)) (λ a → h (g a)) x
after h p f g x with p x
... | true = refl
... | false = refl
