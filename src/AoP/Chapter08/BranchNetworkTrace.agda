{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BranchNetworkTrace where

open import AoP.Common.Prelude
open import AoP.Chapter08.BranchNetwork using (module Network)
open import AoP.Common.NatOrder using (_≤_; rid; sum-mono; weaken)
open import Agda.Builtin.Nat using (Nat)

-- Both child subnets start at the same vertex. Each independently has
-- a cheap and a costly fork. The root must serve both, paying 3 once.
data V : Set where root child stop : V
data Label : Set where station : Label
data Stop : Label → V → Set where arrive : Stop station stop
data Fork : Label → V → V → V → Set where
  trunk : Fork station root child child
  cheap costly : Fork station child stop stop
weight : ∀ {j u v w} → Fork j u v w → Nat
weight trunk = 3
weight cheap = 1
weight costly = 4
open Network Stop Fork weight
leaf = tip station
pair = node station leaf leaf
shape = node station pair pair
fast slow : Route pair child
fast = fork cheap (end arrive) (end arrive)
slow = fork costly (end arrive) (end arrive)

-- Replace first the left route, then the right, keeping trunk fixed.
both-slow : cost (fork trunk slow slow) ≡ 11
both-slow = refl
left-replaced : cost (fork trunk fast slow) ≡ 8
left-replaced = refl
both-replaced : cost (fork trunk fast fast) ≡ 5
both-replaced = refl

child-lower : ∀ (r : Route pair child) → 1 ≤ cost r
child-lower (fork cheap (end arrive) (end arrive)) = rid 1
child-lower (fork costly (end arrive) (end arrive)) = weaken (weaken (weaken (rid 1)))
minimum : ∀ (r : Route shape root) → cost (fork trunk fast fast) ≤ cost r
minimum (fork trunk x y) = sum-mono (rid 3) (sum-mono (child-lower x) (child-lower y))
