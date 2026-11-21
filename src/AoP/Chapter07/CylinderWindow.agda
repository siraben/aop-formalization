{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CylinderWindow where

open import AoP.Common.Prelude
open import AoP.Chapter07.CylinderFiniteRim using (Row; top; below; up; down; last; weaken; advance)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.4. A row-indexed table specifies a lookup; repeated lookup in
-- a linked tuple would walk from the top for each neighbour. Compute
-- the same three-way windows by carrying the previous entry instead.
data Vec (A : Set) : Nat → Set where
  nil : Vec A 0
  cons : ∀ {n} → A → Vec A n → Vec A (suc n)

at : ∀ {A n} → Vec A n → Row n → A
at (cons x xs) top = x
at (cons x xs) (below i) = at xs i

front : ∀ {A n} → Vec A n → A → A
front nil wrap = wrap
front (cons x xs) wrap = x

module Scan {A B : Set} (f : A → A → A → B) where
  sweep : ∀ {n} → A → Vec A n → A → Vec B n
  sweep prev nil wrap = nil
  sweep prev (cons x xs) wrap = cons (f prev x (front xs wrap)) (sweep x xs wrap)

  -- What the sweep reads at an arbitrary row, before closing the rim.
  prevAt nextAt : ∀ {n} → A → Vec A n → Row n → A
  prevAt prev (cons x xs) top = prev
  prevAt prev (cons x xs) (below i) = prevAt x xs i
  nextAt wrap (cons x xs) top = front xs wrap
  nextAt wrap (cons x xs) (below i) = nextAt wrap xs i
  reads : ∀ {n} prev (xs : Vec A n) wrap i → at (sweep prev xs wrap) i ≡ f (prevAt prev xs i) (at xs i) (nextAt wrap xs i)
  reads prev (cons x xs) wrap top = refl
  reads prev (cons x xs) wrap (below i) = reads x xs wrap i

  previous : ∀ {n} x (xs : Vec A n) i → prevAt x xs i ≡ at (cons x xs) (weaken i)
  previous x (cons y ys) top = refl
  previous x (cons y ys) (below i) = previous y ys i

  after : ∀ {n} (xs : Vec A n) wrap (i : Row n) → A
  after xs wrap i with advance i
  ... | inl j = at xs j
  ... | inr _ = wrap
  following : ∀ {n} (xs : Vec A n) wrap i → nextAt wrap xs i ≡ after xs wrap i
  following (cons x nil) wrap top = refl
  following (cons x (cons y ys)) wrap top = refl
  following (cons x xs) wrap (below i) with advance i | following xs wrap i
  ... | inl j | eq = eq
  ... | inr _ | eq = eq

  cyclic : ∀ {n} → Vec A (suc n) → Vec B (suc n)
  cyclic {n} xs = sweep (at xs (last n)) xs (at xs top)
  correct : ∀ {n} (xs : Vec A (suc n)) i → at (cyclic xs) i ≡ f (at xs (up i)) (at xs i) (at xs (down i))
  correct {n} xs i = reads (at xs (last n)) xs (at xs top) i ∙
    (cong (λ a → f a (at xs i) (nextAt (at xs top) xs i)) (u xs i) ∙
     cong (f (at xs (up i)) (at xs i)) (following xs (at xs top) i ∙ d xs i))
    where
      u : ∀ {k} (v : Vec A (suc k)) j → prevAt (at v (last k)) v j ≡ at v (up j)
      u (cons x tail) top = refl
      u (cons x tail) (below j) = previous x tail j
      d : ∀ {k} (v : Vec A (suc k)) j → after v (at v top) j ≡ at v (down j)
      d v j with advance j
      ... | inl h = refl
      ... | inr _ = refl
