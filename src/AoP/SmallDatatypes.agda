{-# OPTIONS --safe --without-K #-}
module AoP.SmallDatatypes where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

-- §1.1. Use seven bits for the book's ASCII alphabet. Each successive
-- bit doubles the number of words. Pairing a character with a Boolean
-- gives 256 possible values; tagging either a character or a Boolean
-- gives 130. Enumerate all of them to check the two counts.
data Bits : Nat → Set where
  end : Bits 0
  bit : ∀ {n} → Bool → Bits n → Bits (suc n)

ASCII = Bits 7
Either = Bool ⊎ ASCII
Both = Bool × ASCII

open import AoP.Horner using (map)
open import AoP.Naturality using (_++_)
open import AoP.Subsequences using (_∈_; here; there; merge; image)

codes : ∀ n → List (Bits n)
codes zero = end ∷ []
codes (suc n) = map (bit false) (codes n) ++ map (bit true) (codes n)

listed : ∀ {n} (c : Bits n) → c ∈ codes n
listed end = here
listed (bit false c) = merge _ _ (inl (image (bit false) (listed c)))
listed (bit true c) = merge (map (bit false) (codes _)) _ (inr (image (bit true) (listed c)))

bools = false ∷ true ∷ []
eithers : List Either
eithers = map inl bools ++ map inr (codes 7)
boths : List Both
boths = map (λ c → false , c) (codes 7) ++ map (λ c → true , c) (codes 7)

len : ∀ {A : Set} → List A → Nat
len [] = 0
len (_ ∷ xs) = suc (len xs)

count-either : len eithers ≡ 130
count-either = refl
count-both : len boths ≡ 256
count-both = refl

neg : Bool → Bool
neg false = true
neg true = false
switch : Both → Both
switch (b , c) = neg b , c
switch-twice : ∀ pair → switch (switch pair) ≡ pair
switch-twice (false , c) = refl
switch-twice (true , c) = refl

cand : Bool → Bool → Bool
cand false _ = false
cand true b = b
and : Bool × Bool → Bool
and (a , b) = cand a b

optional-flag : Maybe Bool
optional-flag = just true
optional-nul : Maybe ASCII
optional-nul = just (bit false (bit false (bit false (bit false (bit false (bit false (bit false end)))))))
