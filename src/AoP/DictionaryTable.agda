{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryTable where

open import AoP.Prelude
open import AoP.DictionarySearch using (module Encode)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Compression using (module Text)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (inl; inr)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (compare)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (nothing; just)

-- For each successive target prefix, scan the previously solved
-- prefixes for one-instruction extensions. Store actual programs and
-- decoding evidence. Literal extension supplies a feasible fallback.
module Table {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A}
  open Encode eq? target using (tokens; list?)
  open Splice {A} c p using (resume; price)
  Cell : List A → Set
  Cell xs = Σ (List Code) λ ps → run [] ps ≡ just xs
  Row = Σ (List A) Cell
  choose : ∀ {xs} → Cell xs → Cell xs → Cell xs
  choose u v with compare (price (fst u)) (price (fst v))
  ... | inl _ = u
  ... | inr _ = v
  reaches? : ∀ xs op ys → Dec (run xs (op ∷ []) ≡ just ys)
  reaches? xs op ys with run xs (op ∷ [])
  ... | nothing = inr (λ ())
  ... | just zs with list? zs ys
  ...   | inr no = inr λ { refl → no refl }
  ...   | inl refl = inl refl
  try : (ys : List A) → Row → Code → Cell ys → Cell ys
  try ys (xs , ps , ok) op best with reaches? xs op ys
  ... | inr _ = best
  ... | inl result = choose ((ps ++ (op ∷ [])) , (resume [] ps (op ∷ []) ok ∙ result)) best
  scan : ∀ ys → Row → List Code → Cell ys → Cell ys
  scan ys row [] best = best
  scan ys row (op ∷ ops) best = scan ys row ops (try ys row op best)
  rows : ∀ ys → List Row → Cell ys → Cell ys
  rows ys [] best = best
  rows ys (r ∷ rs) best = rows ys rs (scan ys r tokens best)
  substCell : ∀ {x y} → x ≡ y → Cell x → Cell y
  substCell refl w = w
  fill : ∀ xs → Cell xs → List Row → (rest : List A) → Cell (xs ++ rest)
  fill xs (ps , ok) old [] = ps , (ok ∙ prefix-law xs [])
  fill xs u old (a ∷ rest) = substCell (assoc xs (a ∷ []) rest) (fill ys next history rest)
    where
    ys = xs ++ (a ∷ [])
    history = (xs , u) ∷ old
    next = rows ys history ((fst u ++ (sym a ∷ [])) , resume [] (fst u) (sym a ∷ []) (snd u))
  encode : Cell target
  encode = fill [] ([] , refl) [] target
