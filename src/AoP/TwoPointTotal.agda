{-# OPTIONS --safe --without-K #-}
module AoP.TwoPointTotal where

open import AoP.Prelude
open import AoP.TwoPointLocale
open import AoP.Complement using (⊥)

-- The diagonal and f°∘f below are valued in opens of the two-point
-- space. At a fixed point p the diagonal is ordinary equality, and
-- composition through the singleton has just one possible midpoint.
Rel : Set → Set → Set₁
Rel B A = B → A → Grade
_⊆_ : ∀ {A B} → Rel B A → Rel B A → Set
R ⊆ S = ∀ b a → R b a ≤ S b a
comp : ∀ {A B C} → Rel C B → Rel B A → Rel C A
comp g f c a = join (λ b → meet (g c b) (f b a))
rev : ∀ {A B} → Rel B A → Rel A B
rev f a b = f b a
idR : ∀ {A} → Rel A A
idR x y _ = x ≡ y
Entire : ∀ {X} → Rel ⊤ X → Set
Entire f = idR ⊆ comp (rev f) f

extract : ∀ {X} (f : Rel ⊤ X) → Entire f → Total (f tt)
extract f ent x p with ent x x p refl
... | tt , fx , _ = fx
introduce : ∀ {X} (f : Rel ⊤ X) → Total (f tt) → Entire f
introduce f all x .x p refl = tt , all x p , all x p

-- Even the factorization requirement of a tabulation is impossible;
-- joint monicity would only impose an additional condition.
scalar : Rel ⊤ ⊤
scalar _ _ = one-point
no-tabulation : ∀ {X} (f g : Rel ⊤ X) → Entire f → Entire g →
                scalar ⊆ comp g (rev f) → comp g (rev f) ⊆ scalar → ⊥
no-tabulation f g ef eg into out = no-span (g tt) (f tt) (extract g eg) (extract f ef) (into tt tt) (out tt tt)
