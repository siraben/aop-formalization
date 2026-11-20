{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.AssociativeBrackets where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin; foldt)
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Chapter01.Naturality using (_++_)

-- Exercise 9.12. Flatten any bracketing to a nonempty sequence of
-- leaves, then fold. Associativity alone makes this equal to directly
-- folding the tree: there is no empty leaf sequence requiring a unit.
module Law {A B : Set} (g : A → B) (_·_ : B → B → B)
           (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c)) where
  cat : Nonempty A → Nonempty A → Nonempty A
  cat (x ∷⁺ xs) (y ∷⁺ ys) = x ∷⁺ (xs ++ (y ∷ ys))

  run : A → List A → B
  run x [] = g x
  run x (y ∷ ys) = g x · run y ys

  append-law : ∀ x xs y ys → run x (xs ++ (y ∷ ys)) ≡ run x xs · run y ys
  append-law x [] y ys = refl
  append-law x (a ∷ as) y ys = cong (g x ·_) (append-law a as y ys) ∙ back (assoc (g x) (run a as) (run y ys))
    where back : ∀ {a b : B} → a ≡ b → b ≡ a
          back refl = refl

  eval : Nonempty A → B
  eval (x ∷⁺ xs) = run x xs
  distribute : ∀ l r → eval (cat l r) ≡ eval l · eval r
  distribute (x ∷⁺ xs) (y ∷⁺ ys) = append-law x xs y ys

  leaves = foldt (λ x → x ∷⁺ []) cat
  fusion : ∀ t → eval (leaves t) ≡ foldt g _·_ t
  fusion (tip x) = refl
  fusion (bin l r) = begin
    eval (cat (leaves l) (leaves r)) ≡⟨ distribute (leaves l) (leaves r) ⟩
    eval (leaves l) · eval (leaves r) ≡⟨ cong (_· eval (leaves r)) (fusion l) ⟩
    foldt g _·_ l · eval (leaves r) ≡⟨ cong (foldt g _·_ l ·_) (fusion r) ⟩
    foldt g _·_ (bin l r) ∎
