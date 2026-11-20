{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryLastEdge where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (suc; zero)

-- Decompose a successful nonempty rival at its final instruction.
-- Its predecessor is strictly earlier in the target, even when the
-- final pointer reads letters newly produced by the same instruction.
module Law {A : Set} where
  open Text {A}
  record Last (start : List A) (ops : List Code) (target : List A) : Set where
    constructor edge
    field
      before : List Code
      op : Code
      state : List A
      split : ops ≡ before ++ (op ∷ [])
      prefix : run start before ≡ just state
      step : run state (op ∷ []) ≡ just target
  decompose : ∀ xs op ops {ys} → run xs (op ∷ ops) ≡ just ys → Last xs (op ∷ ops) ys
  decompose xs op [] ok = edge [] op xs refl refl ok
  decompose xs (sym a) (b ∷ bs) ok with decompose (xs ++ (a ∷ [])) b bs ok
  ... | edge ps op state split prefix step = edge (sym a ∷ ps) op state (cong (sym a ∷_) split) prefix step
  decompose xs (ptr i k) (b ∷ bs) ok with copy i (suc k) xs in copied
  ... | nothing with ok
  ...   | ()
  decompose xs (ptr i k) (b ∷ bs) ok | just ws with decompose ws b bs ok
  ... | edge ps op state split prefix step = edge (ptr i k ∷ ps) op state (cong (ptr i k ∷_) split) run′ step
    where run′ : run xs (ptr i k ∷ ps) ≡ just state
          run′ rewrite copied = prefix

  copy-suffix : ∀ i k xs {ys} → copy i k xs ≡ just ys → Σ (List A) λ zs → xs ++ zs ≡ ys
  copy-suffix i zero xs refl = [] , unit xs
    where unit : ∀ (xs : List A) → xs ++ [] ≡ xs
          unit [] = refl
          unit (x ∷ xs) = cong (x ∷_) (unit xs)
  copy-suffix i (suc k) xs ok with lookup i xs
  ... | nothing with ok
  ...   | ()
  copy-suffix i (suc k) xs ok | just a with copy-suffix (suc i) k (xs ++ (a ∷ [])) ok
  ... | zs , eq rewrite assoc xs (a ∷ []) zs = (a ∷ zs) , eq
  earlier : ∀ xs op {ys} → run xs (op ∷ []) ≡ just ys → Σ A λ a → Σ (List A) λ zs → xs ++ (a ∷ zs) ≡ ys
  earlier xs (sym a) refl = a , [] , refl
  earlier xs (ptr i k) ok with lookup i xs
  ... | nothing with ok
  ...   | ()
  earlier xs (ptr i k) ok | just a with copy (suc i) k (xs ++ (a ∷ [])) in tail
  ... | nothing with ok
  ...   | ()
  earlier xs (ptr i k) refl | just a | just ys with copy-suffix (suc i) k (xs ++ (a ∷ [])) tail
  ... | zs , eq rewrite assoc xs (a ∷ []) zs = a , zs , eq
