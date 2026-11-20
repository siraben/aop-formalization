{-# OPTIONS --safe --without-K #-}
module AoP.ScheduleDuration where

open import AoP.Prelude
open import AoP.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.Tardiness using (Job)
open Job using (duration)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §10.3. When choosing the last job, its finish time is already known:
-- all jobs have run, so permuting them cannot change total duration.
-- This is not true of the penultimate job. The proof below moves the
-- duration of one inserted job past the jobs preceding its new slot.
total : List Job → Nat
total [] = 0
total (j ∷ js) = duration j + total js

private
  plus-suc : ∀ a b → a + suc b ≡ suc (a + b)
  plus-suc zero b = refl
  plus-suc (suc a) b = cong suc (plus-suc a b)

  back : ∀ {a b : Nat} → a ≡ b → b ≡ a
  back refl = refl

  exchange : ∀ a b c → a + (b + c) ≡ b + (a + c)
  exchange zero b c = refl
  exchange (suc a) b c = begin
    suc (a + (b + c)) ≡⟨ cong suc (exchange a b c) ⟩
    suc (b + (a + c)) ≡⟨ back (plus-suc b (a + c)) ⟩
    b + (suc a + c) ∎

insert-total : ∀ {j xs ys} → Insert j xs ys → total ys ≡ duration j + total xs
insert-total front = refl
insert-total {j} (later {x} {xs} {ys} p) = begin
  total (x ∷ ys)                      ≡⟨ cong (duration x +_) (insert-total p) ⟩
  duration x + (duration j + total xs) ≡⟨ exchange (duration x) (duration j) (total xs) ⟩
  duration j + total (x ∷ xs) ∎

perm-total : ∀ {xs ys} → Perm xs ys → total ys ≡ total xs
perm-total empty = refl
perm-total (insert {j} {xs} {ys} {zs} p i) = begin
  total zs              ≡⟨ insert-total i ⟩
  duration j + total ys ≡⟨ cong (duration j +_) (perm-total p) ⟩
  total (j ∷ xs) ∎
