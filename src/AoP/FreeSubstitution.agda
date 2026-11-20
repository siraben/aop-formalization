{-# OPTIONS --safe --without-K #-}
module AoP.FreeSubstitution where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Initial using (module Theory)

-- Exercise 2.40. With variable type A, one syntax layer is either a
-- variable or one G-operation on recursive children. Assume the initial
-- algebras in the question exist. Substituting k for the variables is
-- a fold: replace a variable by k's result, and rebuild each operation.
module Free (G : Functor Fun Fun) where
  private module G = Functor G
  Layer : Set → Functor Fun Fun
  Functor.F₀ (Layer A) X = A ⊎ G.F₀ X
  Functor.F₁ (Layer A) f (inl a) = inl a
  Functor.F₁ (Layer A) f (inr t) = inr (G.F₁ f t)
  Functor.resp (Layer A) eq (inl _) = refl
  Functor.resp (Layer A) eq (inr t) = cong inr (G.resp eq t)
  Functor.identity (Layer A) (inl _) = refl
  Functor.identity (Layer A) (inr t) = cong inr (G.identity t)
  Functor.composition (Layer A) g f (inl _) = refl
  Functor.composition (Layer A) g f (inr t) = cong inr (G.composition g f t)

  module Terms (I : ∀ A → Theory.Initial (Layer A)) where
    module T (A : Set) = Theory.Initial (I A)
    Term = T.μ
    var : ∀ {A} → A → Term A
    var a = T.inn _ (inl a)
    op : ∀ {A} → G.F₀ (Term A) → Term A
    op t = T.inn _ (inr t)

    alg : ∀ {A B} → (A → Term B) → A ⊎ G.F₀ (Term B) → Term B
    alg k (inl a) = k a
    alg k (inr t) = op t
    sub : ∀ {A B} → (A → Term B) → Term A → Term B
    sub {A} k = T.⦅_⦆ A (alg k)

    variable-law : ∀ {A B} (k : A → Term B) a → sub k (var a) ≡ k a
    variable-law {A} k a = T.computation A (alg k) (inl a)

    op-law : ∀ {A B} (k : A → Term B) t → sub k (op t) ≡ op (G.F₁ (sub k) t)
    op-law {A} k t = T.computation A (alg k) (inr t)

    private
      back : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
      back refl = refl

    unchanged : ∀ {A} (t : Term A) → sub var t ≡ t
    unchanged {A} t = back (T.unique A (alg var) (λ x → x) law t)
      where
      law : Theory.Hom (Layer A) (T.inn A) (alg var) (λ x → x)
      law (inl a) = refl
      law (inr s) = cong op (back (G.identity s))

    -- Folding twice agrees with substituting the composite replacement.
    compose : ∀ {A B C} (k : A → Term B) (j : B → Term C) t →
              sub j (sub k t) ≡ sub (λ a → sub j (k a)) t
    compose {A} k j = Theory.Laws.fusion (Layer A) (I A) (alg k) (alg (λ a → sub j (k a))) (sub j) law
      where
      law : Theory.Hom (Layer A) (alg k) (alg (λ a → sub j (k a))) (sub j)
      law (inl a) = refl
      law (inr s) = op-law j s
