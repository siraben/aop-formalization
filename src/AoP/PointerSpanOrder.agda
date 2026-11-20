{-# OPTIONS --safe --without-K #-}
module AoP.PointerSpanOrder where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.DecoderPrefix using (module Law)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (just; nothing)

-- Two copies end at one text. Cancel one trailing character at a
-- time: when the shorter copy runs out, the longer one's remaining
-- path witnesses the required prefix comparison of their start states.
module Order {A : Set} (c p : Nat) where
  open Text {A}
  open Law {A} c p using (Prefix; same; more)
  data Path (xs : List A) : Nat → List A → Set where
    stop : Path xs 0 xs
    snoc : ∀ {ys n} a → Path xs n ys → Path xs (suc n) (ys ++ (a ∷ []))
  prepend : ∀ xs a {n ys} → Path (xs ++ (a ∷ [])) n ys → Path xs (suc n) ys
  prepend xs a stop = snoc a stop
  prepend xs a (snoc b q) = snoc b (prepend xs a q)
  path : ∀ i n xs {ys} → copy i n xs ≡ just ys → Path xs n ys
  path i 0 xs refl = stop
  path i (suc n) xs ok with lookup i xs
  ... | nothing with ok
  ...   | ()
  path i (suc n) xs ok | just a = prepend xs a (path (suc i) n (xs ++ (a ∷ [])) ok)
  forget : ∀ {xs n ys} → Path xs n ys → Prefix xs ys
  forget stop = same
  forget (snoc a q) = more a (forget q)
  init : List A → List A
  init [] = []
  init (_ ∷ []) = []
  init (a ∷ b ∷ bs) = a ∷ init (b ∷ bs)
  cancel : ∀ xs a → init (xs ++ (a ∷ [])) ≡ xs
  cancel [] a = refl
  cancel (x ∷ []) a = refl
  cancel (x ∷ y ∷ ys) a = cong (x ∷_) (cancel (y ∷ ys) a)
  compare : ∀ {xs ys n m u v} → Path xs n u → Path ys m v → m ≤ n → u ≡ v → Prefix xs ys
  compare q stop le refl = forget q
  compare (snoc {ys = u} a q) (snoc {ys = v} b r) (s≤ le) eq = compare q r le (rev (cancel u a) ∙ cong init eq ∙ cancel v b)
    where rev : ∀ {x y : List A} → x ≡ y → y ≡ x
          rev refl = refl
  success : ∀ xs i k {ys} → run xs (ptr i k ∷ []) ≡ just ys → Path xs (suc k) ys
  success xs i k ok with copy i (suc k) xs in eq
  ... | nothing with ok
  ...   | ()
  success xs i k refl | just ys = path i (suc k) xs eq
  starts : ∀ xs ys i j k n {goal} → run xs (ptr i k ∷ []) ≡ just goal → run ys (ptr j n ∷ []) ≡ just goal → n ≤ k → Prefix xs ys
  starts xs ys i j k n p q le = compare (success xs i k p) (success ys j n q) (s≤ le) refl
