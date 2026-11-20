{-# OPTIONS --safe --without-K #-}
module AoP.VanLexOrder where

open import AoP.Prelude
open import AoP.VanHeadOrder using (module Law)
open import AoP.Complement using (⊥)

-- Exercise 7.57. Compare first blocks by prefix. Only when the
-- reverse prefix also holds must the remaining blocks be compared.
module Order (A : Set) where
  open Law A using (Prefix; empty; keep)
  Blocks = List (List A)
  Q : Blocks → Blocks → Set
  Q [] ys = ⊤
  Q (_ ∷ _) [] = ⊥
  Q (x ∷ xs) (y ∷ ys) = Prefix x y × (Prefix y x → Q xs ys)

  reflP : ∀ x → Prefix x x
  reflP [] = empty
  reflP (a ∷ xs) = keep a (reflP xs)
  transP : ∀ {x y z} → Prefix x y → Prefix y z → Prefix x z
  transP empty q = empty
  transP (keep a p) (keep .a q) = keep a (transP p q)
  reflQ : ∀ xs → Q xs xs
  reflQ [] = tt
  reflQ (x ∷ xs) = reflP x , λ _ → reflQ xs
  transQ : ∀ xs ys zs → Q xs ys → Q ys zs → Q xs zs
  transQ [] ys zs p q = tt
  transQ (_ ∷ _) [] zs () q
  transQ (_ ∷ _) (_ ∷ _) [] p ()
  transQ (x ∷ xs) (y ∷ ys) (z ∷ zs) (xy , p) (yz , q) = transP xy yz , λ zx →
    transQ xs ys zs (p (transP yz zx)) (q (transP zx xy))

  fresh : ∀ a xs ys → Q xs ys → Q ((a ∷ []) ∷ xs) ((a ∷ []) ∷ ys)
  fresh a xs ys q = reflP (a ∷ []) , λ _ → q
  tails : ∀ {a b xs ys} → Prefix (a ∷ xs) (b ∷ ys) → Prefix xs ys
  tails (keep _ p) = p
  glue : ∀ a x xs y ys → Q (x ∷ xs) (y ∷ ys) → Q ((a ∷ x) ∷ xs) ((a ∷ y) ∷ ys)
  glue a x xs y ys (p , q) = keep a p , λ r → q (tails r)
