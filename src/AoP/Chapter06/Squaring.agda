{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Squaring where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.Common.Prelude

-- §6.4. Reading a digit after a prefix doubles its value and adds the
-- digit. Leading zeroes are harmless: correctness is stated for all words.
data Bits : Set where
  end : Bits
  _O _I : Bits → Bits

value : Bits → Nat
value end = zero
value (bs O) = value bs + value bs
value (bs I) = suc (value bs + value bs)

module Powers {M : Set} (e : M) (_⋆_ : M → M → M)
              (left-unit : ∀ u → e ⋆ u ≡ u)
              (assoc : ∀ u v w → (u ⋆ v) ⋆ w ≡ u ⋆ (v ⋆ w)) (x : M) where
  power : Nat → M
  power zero = e
  power (suc n) = x ⋆ power n

  back : ∀ {u v : M} → u ≡ v → v ≡ u
  back refl = refl

  add : ∀ n m → power (n + m) ≡ power n ⋆ power m
  add zero m = back (left-unit (power m))
  add (suc n) m = begin
    x ⋆ power (n + m)           ≡⟨ cong (x ⋆_) (add n m) ⟩
    x ⋆ (power n ⋆ power m)     ≡⟨ back (assoc x (power n) (power m)) ⟩
    power (suc n) ⋆ power m ∎

  square : M → M
  square u = u ⋆ u

  fast : Bits → M
  fast end = e
  fast (bs O) = square (fast bs)
  fast (bs I) = x ⋆ square (fast bs)

  correct : ∀ bs → fast bs ≡ power (value bs)
  correct end = refl
  correct (bs O) = begin
    square (fast bs)         ≡⟨ cong square (correct bs) ⟩
    square (power (value bs)) ≡⟨ back (add (value bs) (value bs)) ⟩
    power (value (bs O)) ∎
  correct (bs I) = begin
    x ⋆ square (fast bs)          ≡⟨ cong (λ u → x ⋆ square u) (correct bs) ⟩
    x ⋆ square (power (value bs)) ≡⟨ cong (x ⋆_) (back (add (value bs) (value bs))) ⟩
    power (value (bs I)) ∎
