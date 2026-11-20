{-# OPTIONS --safe --without-K #-}
module AoP.EditMinimum where

open import AoP.Prelude
open import AoP.EditScript using (module Scripts)
open import AoP.NatOrder using (_≤_; rid; chain; s≤; compare)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- §9.2. Minimise the number of operations, counting a copy as one (not
-- zero). A substitution costs two: delete, then insert. To justify a cell
-- of the dynamic-programming table, consider the first operation of *any*
-- competitor. A deletion and insertion each refer to a neighbouring cell;
-- a copy refers to the diagonal, but only when the two heads agree.
module Distance {A : Set} (equal? : (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  open Scripts {A}
  cost : ∀ {xs ys} → Script xs ys → Nat
  cost done = 0
  cost (cpy s) = suc (cost s)
  cost (del s) = suc (cost s)
  cost (ins s) = suc (cost s)

  Best : List A → List A → Set
  Best xs ys = Σ (Script xs ys) λ s → (q : Script xs ys) → cost s ≤ cost q

  -- A pool contains a real script and a lower bound for each competitor
  -- in its own branch. Merging pools preserves a bound on either branch.
  Pool : ∀ {xs ys} → (Script xs ys → Set) → Set
  Pool {xs} {ys} P = Σ (Script xs ys) λ s → ∀ q → P q → cost s ≤ cost q

  merge : ∀ {xs ys} {P Q : Script xs ys → Set} → Pool P → Pool Q → Pool (λ q → P q ⊎ Q q)
  merge (p , l) (q , r) with compare (cost p) (cost q)
  ... | inl le = p , λ s → λ { (inl v) → l s v ; (inr v) → chain le (r s v) }
  ... | inr ge = q , λ s → λ { (inl v) → chain ge (l s v) ; (inr v) → r s v }

  module Cell (x y : A) (xs ys : List A) where
    S = Script (x ∷ xs) (y ∷ ys)
    data D : S → Set where d : ∀ p → D (del p)
    data I : S → Set where i : ∀ p → I (ins p)
    deletes : Best xs (y ∷ ys) → Pool D
    deletes (p , l) = del p , λ { _ (d q) → s≤ (l q) }
    inserts : Best (x ∷ xs) ys → Pool I
    inserts (p , l) = ins p , λ { _ (i q) → s≤ (l q) }

  -- Eliminate a competitor before specializing its head letters. This
  -- avoids assuming uniqueness of equality proofs when both heads match.
  cases : ∀ {x y xs ys n} →
    ((q : Script xs ys) → x ≡ y → n ≤ suc (cost q)) →
    ((q : Script xs (y ∷ ys)) → n ≤ suc (cost q)) →
    ((q : Script (x ∷ xs) ys) → n ≤ suc (cost q)) →
    (q : Script (x ∷ xs) (y ∷ ys)) → n ≤ cost q
  cases c d i (cpy q) = c q refl
  cases c d i (del q) = d q
  cases c d i (ins q) = i q

  -- Spend one source head to obtain the previous row. Inside each row,
  -- recurse on the target tail. Both recursions are structural.
  row : (xs ys : List A) → Best xs ys
  row [] [] = done , λ { done → rid 0 }
  row [] (y ∷ ys) with row [] ys
  ... | p , opt = ins p , λ { (ins q) → s≤ (opt q) }
  row (x ∷ xs) ys = build ys
    where
    build : (zs : List A) → Best (x ∷ xs) zs
    build [] with row xs []
    ... | p , opt = del p , λ { (del q) → s≤ (opt q) }
    build (y ∷ zs) with equal? x y
    ... | inr neq with merge (Cell.deletes x y xs zs (row xs (y ∷ zs))) (Cell.inserts x y xs zs (build zs))
    ...   | p , bound = p , λ where
      (del q) → bound _ (inl (Cell.d q))
      (ins q) → bound _ (inr (Cell.i q))
      (cpy q) → impossible (neq refl)
        where impossible : ∀ {T : Set} → ⊥ → T
              impossible ()
    build (.x ∷ zs) | inl refl with row xs zs | merge (Cell.deletes x x xs zs (row xs (x ∷ zs))) (Cell.inserts x x xs zs (build zs))
    ... | r , opt | p , bound with compare (suc (cost r)) (cost p)
    ...   | inl le = cpy r , cases (λ q _ → s≤ (opt q))
      (λ q → chain le (bound _ (inl (Cell.d q))))
      (λ q → chain le (bound _ (inr (Cell.i q))))
    ...   | inr ge = p , cases (λ q _ → chain ge (s≤ (opt q)))
      (λ q → bound _ (inl (Cell.d q))) (λ q → bound _ (inr (Cell.i q)))
