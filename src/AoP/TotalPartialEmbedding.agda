{-# OPTIONS --safe --without-K #-}
module AoP.TotalPartialEmbedding where

open import AoP.Prelude
open import AoP.PartialGraphCategory using (Partial; partial; Par; module Partial)
open import AoP.Categories using (Fun; Category)
open import AoP.Functors using (Functor)

-- §2.1: regard each total function as a partial function with one
-- output on every input. For composition the intermediate witness is
-- exactly f x. Conversely, eliminating that witness recovers g (f x).
total : ∀ {A B : Set} → (A → B) → Partial A B
total f = partial (λ y x → f x ≡ y) λ { refl refl → refl }
private
  back : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
  back refl = refl
include : Functor Fun Par
Functor.F₀ include A = A
Functor.F₁ include = total
Functor.resp include eq = (λ { {a = x} p → back (eq x) ∙ p }) , (λ { {a = x} p → eq x ∙ p })
Functor.identity include = back , back
Functor.composition include g f = (λ { {a = x} eq → f x , (eq , refl) }) , (λ { (y , (p , refl)) → p })

faithful : ∀ {A B : Set} (f g : A → B) → Category._≈_ Par (total f) (total g) → ∀ x → f x ≡ g x
faithful f g eq x = snd eq {b = g x} {a = x} refl
