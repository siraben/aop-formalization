{-# OPTIONS --safe --without-K #-}
module AoP.ChoiceCoverage where

open import AoP.Prelude
open import AoP.Subsequences using (_∈_; here; there; split; merge; preimage; image)
open import AoP.Polynomial using (Poly; I; K; _⊗_; _⊕_; ⟦_⟧; inl; inr)
open import AoP.PolynomialChoices using (cross; listcp)
open import AoP.Horner using (map)
open import AoP.Complement using (⊥)

pair-in : ∀ {A B : Set} {x : A} {y : B} xs ys → x ∈ xs → y ∈ ys → (x , y) ∈ cross xs ys
pair-in (a ∷ xs) ys here n = merge (map (a ,_) ys) (cross xs ys) (inl (image (a ,_) n))
pair-in (a ∷ xs) ys (there m) n = merge (map (a ,_) ys) (cross xs ys) (inr (pair-in xs ys m n))

pair-out : ∀ {A B : Set} {x : A} {y : B} xs ys → (x , y) ∈ cross xs ys → (x ∈ xs) × (y ∈ ys)
pair-out (a ∷ xs) ys m with split (map (a ,_) ys) (cross xs ys) m
... | inl q with preimage (a ,_) ys q
...   | b , n , refl = here , n
pair-out (a ∷ xs) ys m | inr q with pair-out xs ys q
... | l , r = there l , r

-- Relational lifting of membership: keep the shape and constants,
-- and select one menu member at each variable position independently.
Pick : ∀ F {A : Set} → ⟦ F ⟧ A → ⟦ F ⟧ (List A) → Set
Pick I x xs = x ∈ xs
Pick (K C) x c = x ≡ c
Pick (F ⊗ G) (x , y) (u , v) = Pick F x u × Pick G y v
Pick (F ⊕ G) (inl x) (inl u) = Pick F x u
Pick (F ⊕ G) (inr y) (inr v) = Pick G y v
Pick (F ⊕ G) (inl _) (inr _) = ⊥
Pick (F ⊕ G) (inr _) (inl _) = ⊥

complete : ∀ F {A : Set} (x : ⟦ F ⟧ A) u → Pick F x u → x ∈ listcp F u
complete I x xs m = m
complete (K _) x _ refl = here
complete (F ⊗ G) (x , y) (u , v) (p , q) = pair-in _ _ (complete F x u p) (complete G y v q)
complete (F ⊕ G) (inl x) (inl u) p = image inl (complete F x u p)
complete (F ⊕ G) (inr y) (inr v) p = image inr (complete G y v p)

sound : ∀ F {A : Set} (x : ⟦ F ⟧ A) u → x ∈ listcp F u → Pick F x u
sound I x xs m = m
sound (K _) x _ here = refl
sound (K _) x _ (there ())
sound (F ⊗ G) (x , y) (u , v) m with pair-out (listcp F u) (listcp G v) m
... | p , q = sound F x u p , sound G y v q
sound (F ⊕ G) x (inl u) m with preimage inl (listcp F u) m
... | y , p , refl = sound F y u p
sound (F ⊕ G) x (inr v) m with preimage inr (listcp G v) m
... | y , p , refl = sound G y v p
