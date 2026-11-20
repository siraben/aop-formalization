{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BackwardSchedule where

open import AoP.Common.Prelude
open import AoP.Chapter10.ScheduleDuration using (total)
open import AoP.Chapter10.PickLast
open import AoP.Chapter05.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.Chapter10.PermuteRemoval using (commute)
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import AoP.Chapter10.Tardiness using (Job)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §10.3. Pick the last job at the finish time of the *current* bag,
-- schedule the remaining jobs, then append the selected occurrence.
-- The intermediate proof permutes the remainder, not the whole bag.
-- Reinsert transports this proof back to the original input order.
reinsert : ∀ {A : Set} {j : A} {xs ys zs ws} → Insert j xs ys →
           Perm xs zs → Insert j zs ws → Perm ys ws
reinsert front p i = insert p i
reinsert (later r) (insert p i) j with commute i j
... | _ , k , l = insert (reinsert r p k) l

snoc : List Job → Job → List Job
snoc [] j = j ∷ []
snoc (x ∷ xs) j = x ∷ snoc xs j

last-slot : ∀ xs j → Insert j xs (snoc xs j)
last-slot [] j = front
last-slot (x ∷ xs) j = later (last-slot xs j)

length : List Job → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

shrinks : ∀ {j xs ys} → Insert j xs ys → length ys ≡ suc (length xs)
shrinks front = refl
shrinks (later r) = cong suc (shrinks r)

smaller : ∀ {xs ys n j} → Insert j xs ys → length ys ≤ suc n → length xs ≤ n
smaller r bound rewrite shrinks r with bound
... | s≤ b = b

-- The recursive witness records precisely the greedy choices; retaining
-- it permits a subsequent optimality proof without unfolding the program.
data Run : List Job → List Job → Set where
  stop : Run [] []
  choose : ∀ j js {out} → (p : Pick (total (j ∷ js)) (j ∷ js)) →
           Run (Pick.others p) out → Run (j ∷ js) (snoc out (Pick.last p))

permutation : ∀ {xs ys} → Run xs ys → Perm xs ys
permutation stop = empty
permutation (choose j js p r) = reinsert (Pick.restore p) (permutation r) (last-slot _ _)

loop : ∀ n xs → length xs ≤ n → Σ _ (Run xs)
loop n [] _ = [] , stop
loop (suc n) (j ∷ js) b with pick-last j js
... | p with loop n (Pick.others p) (smaller (Pick.restore p) b)
...   | out , rec = snoc out (Pick.last p) , choose j js p rec

schedule : ∀ xs → Σ _ (Run xs)
schedule xs = loop (length xs) xs (rid _)
