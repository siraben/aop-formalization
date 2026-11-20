{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.TipTraversalWork where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Chapter03.TipTraversal using (tipcat; tips)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
private variable A : Set

-- §3.5. Count newly constructed list cells in the suffix traversal.
-- Its suffix already exists; it contributes no cells to the count.
-- The right subtree extends that suffix first. The left subtree then
-- receives the resulting list directly, without copying its spine.
leaves : Tree A → Nat
leaves (tip _) = 1
leaves (bin l r) = leaves l + leaves r

run : Tree A → List A → List A × Nat
run (tip a) ys = (a ∷ ys) , 1
run (bin l r) ys with run r ys
... | suffix , right-count with run l suffix
...   | result , left-count = result , (left-count + right-count)

exact : ∀ (t : Tree A) ys → run t ys ≡ (tipcat t ys , leaves t)
exact (tip a) ys = refl
exact (bin l r) ys rewrite exact r ys | exact l (tipcat r ys) = refl

-- For comparison, the append-based traversal copies every cell in a
-- left child's list at a fork. Charge that copy explicitly, in addition
-- to the singleton allocated at each tip. The skewed tree below always
-- puts the preceding tree on the left, so those copies accumulate.
slow-cost : Tree A → Nat
slow-cost (tip _) = 1
slow-cost (bin l r) = (slow-cost l + slow-cost r) + leaves l

-- Relate the charge to the executable append: every cons in its left
-- argument is copied once, even if the right argument is empty.
length : List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)
copy : List A → List A → List A × Nat
copy [] ys = ys , 0
copy (x ∷ xs) ys with copy xs ys
... | zs , k = (x ∷ zs) , suc k
copy-exact : ∀ (xs ys : List A) → copy xs ys ≡ (xs ++ ys , length xs)
copy-exact [] ys = refl
copy-exact (x ∷ xs) ys rewrite copy-exact xs ys = refl
len-append : ∀ (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
len-append [] ys = refl
len-append (x ∷ xs) ys = cong suc (len-append xs ys)
len-tips : ∀ (t : Tree A) → length (tips t) ≡ leaves t
len-tips (tip _) = refl
len-tips (bin l r) rewrite len-append (tips l) (tips r) | len-tips l | len-tips r = refl
slow : Tree A → List A × Nat
slow (tip a) = (a ∷ []) , 1
slow (bin l r) with slow l | slow r
... | xs , n | ys , m with copy xs ys
...   | zs , k = zs , ((n + m) + k)
slow-exact : ∀ (t : Tree A) → slow t ≡ (tips t , slow-cost t)
slow-exact (tip _) = refl
slow-exact (bin l r) rewrite slow-exact l | slow-exact r | copy-exact (tips l) (tips r) | len-tips l = refl

comb : Nat → Tree Nat
comb zero = tip 0
comb (suc n) = bin (comb n) (tip (suc n))

private
  plus-one : ∀ n → n + 1 ≡ suc n
  plus-one zero = refl
  plus-one (suc n) = cong suc (plus-one n)

comb-leaves : ∀ n → leaves (comb n) ≡ suc n
comb-leaves zero = refl
comb-leaves (suc n) rewrite comb-leaves n = plus-one (suc n)

-- n counts forks. Adding a fork adds one singleton and copies n+1
-- cells. For three forks the four-cell answer costs 1+2+3+4 = 10.
comb-step : ∀ n → slow-cost (comb (suc n)) ≡ (slow-cost (comb n) + 1) + suc n
comb-step n = cong ((slow-cost (comb n) + 1) +_) (comb-leaves n)
contrast : _≡_ {A = Nat × Nat} (slow-cost (comb 3) , snd (run (comb 3) [])) (10 , 4)
contrast = refl

-- Separate the existing suffix from the allocated prefix in the trace:
-- 4 was already present. The right tip adds 3, then the left fork adds
-- 2 and 1 in that order. The final list is still in left-to-right order.
trace : run (bin (bin (tip 1) (tip 2)) (tip 3)) (4 ∷ []) ≡ ((1 ∷ 2 ∷ 3 ∷ 4 ∷ []) , 3)
trace = begin
  run (bin (bin (tip 1) (tip 2)) (tip 3)) (4 ∷ []) ≡⟨⟩
  (fst (run (bin (tip 1) (tip 2)) (3 ∷ 4 ∷ [])) , (2 + 1)) ≡⟨⟩
  ((1 ∷ 2 ∷ 3 ∷ 4 ∷ []) , 3) ∎
