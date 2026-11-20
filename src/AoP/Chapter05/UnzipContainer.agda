{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.UnzipContainer where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)

-- Exercise 5.10 for containers. The input shape fixes all positions,
-- even when infinitely many are present. Separate output witnesses can
-- therefore be paired at each position without collecting choices.
module Law (Shape : Set) (Pos : Shape → Set) where
  C : Set → Set
  C A = Σ Shape λ s → Pos s → A
  data Lift {A B : Set} (R : B ← A) : C B ← C A where
    lift : ∀ {s} {f : Pos s → B} {g : Pos s → A} → (∀ i → R (f i) (g i)) → Lift R (s , f) (s , g)
  -- Unzip is the pair of lifted projection graphs. Output position
  -- functions need only agree pointwise, avoiding function extensionality.
  Unzip : ∀ {A B} → (C A × C B) ← C (A × B)
  Unzip (l , r) v = Lift (λ x z → x ≡ fst z) l v × Lift (λ y z → y ≡ snd z) r v
  module Natural {A B D E : Set} (R : D ← A) (S : E ← B) where
    P : (D × E) ← (A × B)
    P u v = R (fst u) (fst v) × S (snd u) (snd v)
    Q : (C D × C E) ← (C A × C B)
    Q u v = Lift R (fst u) (fst v) × Lift S (snd u) (snd v)
    subst-left : ∀ {X Y : Set} (T : X ← Y) {x x′ y} → x′ ≡ x → T x y → T x′ y
    subst-left T refl p = p
    forward : Unzip ∘ Lift P ⊆ Q ∘ Unzip
    forward {a = s , g} (_ , (lift l , lift r) , lift p) =
      ((s , (λ i → fst (g i))) , (s , (λ i → snd (g i)))) ,
      (lift (λ i → subst-left R (l i) (fst (p i))) , lift (λ i → subst-left S (r i) (snd (p i)))) ,
      lift (λ _ → refl) , lift (λ _ → refl)
    backward : Q ∘ Unzip ⊆ Unzip ∘ Lift P
    backward {b = (s , f) , (_ , h)} (_ , (lift p , lift q) , lift l , lift r) =
      (s , (λ i → f i , h i)) , (lift (λ _ → refl) , lift (λ _ → refl)) , lift (λ i → transport R (l i) (p i) , transport S (r i) (q i))
      where transport : ∀ {X Y : Set} (T : X ← Y) {x y y′} → y ≡ y′ → T x y → T x y′
            transport T refl e = e
