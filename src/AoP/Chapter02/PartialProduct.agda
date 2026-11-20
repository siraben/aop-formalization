{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.PartialProduct where

open import AoP.Common.Prelude
open import AoP.Chapter02.PartialHead using (bind)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
private variable A B X : Set

-- Exercise 2.30. For two partial functions on a common input, the left
-- result may exist alone, the right alone, or both together. These three
-- cases are the product object. When neither exists, pairing is undefined.
data BothOrOne (A B : Set) : Set where
  onlyL : A → BothOrOne A B
  onlyR : B → BothOrOne A B
  both : A → B → BothOrOne A B

left : BothOrOne A B → Maybe A
left (onlyL a) = just a
left (onlyR b) = nothing
left (both a b) = just a
right : BothOrOne A B → Maybe B
right (onlyL a) = nothing
right (onlyR b) = just b
right (both a b) = just b

pack : Maybe A → Maybe B → Maybe (BothOrOne A B)
pack nothing nothing = nothing
pack (just a) nothing = just (onlyL a)
pack nothing (just b) = just (onlyR b)
pack (just a) (just b) = just (both a b)

projectL : (a : Maybe A) (b : Maybe B) → bind (pack a b) left ≡ a
projectL nothing nothing = refl
projectL nothing (just _) = refl
projectL (just _) nothing = refl
projectL (just _) (just _) = refl
projectR : (a : Maybe A) (b : Maybe B) → bind (pack a b) right ≡ b
projectR nothing nothing = refl
projectR nothing (just _) = refl
projectR (just _) nothing = refl
projectR (just _) (just _) = refl

rebuild : (v : Maybe (BothOrOne A B)) → v ≡ pack (bind v left) (bind v right)
rebuild nothing = refl
rebuild (just (onlyL a)) = refl
rebuild (just (onlyR b)) = refl
rebuild (just (both a b)) = refl

unique : (h : X → Maybe (BothOrOne A B)) (f : X → Maybe A) (g : X → Maybe B) →
         (∀ x → bind (h x) left ≡ f x) → (∀ x → bind (h x) right ≡ g x) →
         ∀ x → h x ≡ pack (f x) (g x)
unique h f g l r x = begin
  h x ≡⟨ rebuild (h x) ⟩
  pack (bind (h x) left) (bind (h x) right) ≡⟨ cong (λ a → pack a (bind (h x) right)) (l x) ⟩
  pack (f x) (bind (h x) right) ≡⟨ cong (pack (f x)) (r x) ⟩
  pack (f x) (g x) ∎
