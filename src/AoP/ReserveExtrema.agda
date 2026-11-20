{-# OPTIONS --safe --without-K #-}
module AoP.ReserveExtrema where

open import AoP.Prelude
open import AoP.Reserves using (Tx; deposit; withdraw)
open import AoP.NatOrder using (_≤_; z≤; s≤; weaken; rid)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

-- §7.5. Cache the negative floor and positive ceiling of the running
-- transaction sums. They are the stock and free space a block requires
-- at entry. For [+2,−5,+7] the requirements are three and four: in a
-- vault of size ten any starting balance from three through six works.
record Needs : Set where
  constructor need
  field stock space : Nat

extend : Tx → Needs → Needs
extend (deposit n) (need l h) = need (l - n) (n + h)
extend (withdraw n) (need l h) = need (n + l) (h - n)

summary : List Tx → Needs
summary [] = need 0 0
summary (t ∷ ts) = extend t (summary ts)

example : summary (deposit 2 ∷ withdraw 5 ∷ deposit 7 ∷ []) ≡ need 3 4
example = refl

-- Express balance and headroom separately. A deposit transfers n units
-- from headroom to balance; withdrawal transfers them in reverse. The
-- lower-bound residuation below justifies the truncated differences.
Fits : Needs → Nat → Nat → Set
Fits (need l h) r s = (l ≤ r) × (h ≤ s)

shift : ∀ l n r → (l - n) ≤ r → l ≤ (n + r)
shift l zero r p = p
shift zero (suc n) r p = z≤
shift (suc l) (suc n) r p = s≤ (shift l n r p)

unshift : ∀ l n r → l ≤ (n + r) → (l - n) ≤ r
unshift l zero r p = p
unshift zero (suc n) r p = z≤
unshift (suc l) (suc n) r (s≤ p) = unshift l n r p

strip : ∀ n {a b} → (n + a) ≤ (n + b) → a ≤ b
strip zero p = p
strip (suc n) (s≤ p) = strip n p

lift : ∀ n {a b} → a ≤ b → (n + a) ≤ (n + b)
lift zero p = p
lift (suc n) p = s≤ (lift n p)

credit-in : ∀ n q r s → Fits (extend (deposit n) q) r (n + s) → Fits q (n + r) s
credit-in n (need l h) r s (lp , hp) = shift l n r lp , strip n hp

credit-out : ∀ n q r s → Fits q (n + r) s → Fits (extend (deposit n) q) r (n + s)
credit-out n (need l h) r s (lp , hp) = unshift l n r lp , lift n hp

debit-in : ∀ n q r s → Fits (extend (withdraw n) q) (n + r) s → Fits q r (n + s)
debit-in n (need l h) r s (lp , hp) = strip n lp , shift h n s hp

debit-out : ∀ n q r s → Fits q r (n + s) → Fits (extend (withdraw n) q) (n + r) s
debit-out n (need l h) r s (lp , hp) = lift n lp , unshift h n s hp
