{-# OPTIONS --safe --without-K #-}
module AoP.SignedSegment where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import AoP.NatOrder as N using ()
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.MaximumSegment using (module Solve)

-- §7.2. On [-5,4,-1,3,-7] the segment [4,-1,3] wins with 6.
-- Signed scores allow a winning segment to start and end strictly
-- inside the input and to include a negative entry between gains.
data _≤_ : Int → Int → Set where
  pp : ∀ {a b} → a N.≤ b → pos a ≤ pos b
  nn : ∀ {a b} → b N.≤ a → negsuc a ≤ negsuc b
  np : ∀ {a b} → negsuc a ≤ pos b

rid : ∀ a → a ≤ a
rid (pos n) = pp (N.rid n)
rid (negsuc n) = nn (N.rid n)
chain : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
chain (pp p) (pp q) = pp (N.chain p q)
chain (nn p) (nn q) = nn (N.chain q p)
chain np (pp _) = np
chain (nn _) np = np
cmp : ∀ a b → (a ≤ b) ⊎ (b ≤ a)
cmp (pos a) (pos b) with N.compare a b
... | inl p = inl (pp p)
... | inr p = inr (pp p)
cmp (negsuc a) (negsuc b) with N.compare a b
... | inl p = inr (nn p)
... | inr p = inl (nn p)
cmp (pos _) (negsuc _) = inr np
cmp (negsuc _) (pos _) = inl np

up down : Int → Int
up (pos n) = pos (suc n)
up (negsuc zero) = pos 0
up (negsuc (suc n)) = negsuc n
down (negsuc n) = negsuc (suc n)
down (pos zero) = negsuc 0
down (pos (suc n)) = pos n

up-mono : ∀ {a b} → a ≤ b → up a ≤ up b
up-mono (pp p) = pp (N.s≤ p)
up-mono (nn {zero} N.z≤) = pp N.z≤
up-mono (nn {suc _} N.z≤) = np
up-mono (nn (N.s≤ p)) = nn p
up-mono (np {zero}) = pp N.z≤
up-mono (np {suc _}) = np

down-mono : ∀ {a b} → a ≤ b → down a ≤ down b
down-mono (nn p) = nn (N.s≤ p)
down-mono (pp {b = zero} N.z≤) = nn N.z≤
down-mono (pp {b = suc _} N.z≤) = np
down-mono (pp (N.s≤ p)) = pp p
down-mono (np {b = zero}) = nn N.z≤
down-mono (np {b = suc _}) = np

repeat : Nat → (Int → Int) → Int → Int
repeat zero f x = x
repeat (suc n) f x = f (repeat n f x)
repeat-mono : ∀ n f → (∀ {a b} → a ≤ b → f a ≤ f b) → ∀ {a b} → a ≤ b → repeat n f a ≤ repeat n f b
repeat-mono zero f m p = p
repeat-mono (suc n) f m p = m (repeat-mono n f m p)

add : Int → Int → Int
add (pos n) = repeat n up
add (negsuc n) = repeat (suc n) down
mono : ∀ x {a b} → a ≤ b → add x a ≤ add x b
mono (pos n) = repeat-mono n up up-mono
mono (negsuc n) = repeat-mono (suc n) down down-mono

module M = Solve (pos 0) add _≤_ rid chain cmp mono
sample = negsuc 4 ∷ pos 4 ∷ negsuc 0 ∷ pos 3 ∷ negsuc 6 ∷ []
maximum : M.Max.score (snd (M.scan sample)) ≡ pos 6
maximum = refl
witness : M.Segment sample (pos 6)
witness = M.later (M.start (M.extend (M.extend (M.extend M.empty))))
