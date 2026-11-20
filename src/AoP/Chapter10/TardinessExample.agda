{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TardinessExample where

open import AoP.Common.Prelude
open import AoP.Chapter10.Tardiness
open import AoP.Common.NatOrder using (_≤_; rid; weaken)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_)

-- §10.3. Why build a schedule backwards? For these three jobs *any*
-- order finishes at time 30. The job placed last therefore incurs a
-- penalty of 20, 30, or 30, respectively. No schedule can beat 20.
-- Enumerate the six orders to check attainment and the competing costs.
A B C : Job
A = job 5 10 1
B = job 10 20 3
C = job 15 20 3

data Order : Set where abc acb bac bca cab cba : Order

schedule : Order → Snoc Job
schedule abc = ((ε ▻ A) ▻ B) ▻ C
schedule acb = ((ε ▻ A) ▻ C) ▻ B
schedule bac = ((ε ▻ B) ▻ A) ▻ C
schedule bca = ((ε ▻ B) ▻ C) ▻ A
schedule cab = ((ε ▻ C) ▻ A) ▻ B
schedule cba = ((ε ▻ C) ▻ B) ▻ A

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

pad : ∀ n k → n ≤ k + n
pad n zero = rid n
pad n (suc k) = weaken (pad n k)

minimum : ∀ order → cost (schedule bca) ≤ cost (schedule order)
minimum abc = pad 20 10
minimum acb = pad 20 10
minimum bac = pad 20 10
minimum bca = rid 20
minimum cab = pad 20 10
minimum cba = rid 20

other-optimum : cost (schedule cba) ≡ cost (schedule bca)
other-optimum = refl
