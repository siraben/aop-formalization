{-# OPTIONS --safe --without-K #-}
module AoP.PermutedValue where

open import AoP.Prelude
open import AoP.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.BracketSpine using (leaves)
open import AoP.Trees using (Tree; tip; bin; foldt)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

-- Exercise 9.15: a reordered tree preserves the result even if the
-- operation has no unit. Use an optional accumulator for empty lists.
module Law {A B : Set} (g : A → B) (_·_ : B → B → B)
           (assoc : ∀ a b c → (a · b) · c ≡ a · (b · c))
           (comm : ∀ a b → a · b ≡ b · a) where
  back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  back refl = refl
  push : B → Maybe B → Maybe B
  push a nothing = just a
  push a (just b) = just (a · b)
  swap : ∀ a b z → push a (push b z) ≡ push b (push a z)
  swap a b nothing = cong just (comm a b)
  swap a b (just c) = cong just (back (assoc a b c) ∙ cong (_· c) (comm a b) ∙ assoc b a c)
  run : List A → Maybe B → Maybe B
  run [] z = z
  run (x ∷ xs) z = push (g x) (run xs z)
  place : ∀ {a xs ys} → Insert a xs ys → ∀ z → run ys z ≡ push (g a) (run xs z)
  place front z = refl
  place (later {x} p) z = cong (push (g x)) (place p z) ∙ swap (g x) _ _
  perm : ∀ {xs ys} → Perm xs ys → ∀ z → run ys z ≡ run xs z
  perm empty z = refl
  perm (insert {a} p i) z = place i z ∙ cong (push (g a)) (perm p z)

  append : ∀ xs ys z → run (xs ++ ys) z ≡ run xs (run ys z)
  append [] ys z = refl
  append (x ∷ xs) ys z = cong (push (g x)) (append xs ys z)
  val = foldt g _·_
  fuse : ∀ t z → run (leaves t) z ≡ push (val t) z
  fuse (tip x) z = refl
  fuse (bin l r) z = append (leaves l) (leaves r) z ∙ cong (run (leaves l)) (fuse r z) ∙ fuse l (push (val r) z) ∙ combine z
    where combine : ∀ u → push (val l) (push (val r) u) ≡ push (val l · val r) u
          combine nothing = refl
          combine (just b) = cong just (back (assoc (val l) (val r) b))
  invariant : ∀ t u → Perm (leaves t) (leaves u) → val u ≡ val t
  invariant t u p = inject (back (fuse u nothing) ∙ perm p nothing ∙ fuse t nothing)
    where inject : ∀ {a b : B} → just a ≡ just b → a ≡ b
          inject refl = refl
