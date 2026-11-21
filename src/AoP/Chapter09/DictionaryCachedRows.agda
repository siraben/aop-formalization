{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryCachedRows where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionaryCachedSize using (module Cache)
open import AoP.Chapter09.LongestPointerScan using (module Scan)
open import AoP.Chapter09.ReducedDictionary using (module Reduced)
import AoP.Chapter09.ReducedDictionaryOptimal as Optimal
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.NatOrder using (compare; _≤_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

-- §9.4. Cache a price beside each solved prefix. The longest-pointer
-- search supplies the occurrence of its predecessor in the row list;
-- that occurrence retrieves the *same program's* certified price.
module Rows {A : Set} (eq? : ∀ (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A} hiding (lookup)
  module T = Table eq? target c p
  module C = Cache {A} c p
  module R = Reduced eq? target c p
  open Splice {A} c p using (price; resume)
  record Cost (ps : List Code) : Set where
    constructor cached
    field value : Nat
          exact : value ≡ price ps
  open Cost
  data Costs : List T.Row → Set where
    nil : Costs []
    cons : ∀ {xs u rs} → Cost (fst u) → Costs rs → Costs ((xs , u) ∷ rs)
  lookup : ∀ {rs r} → Costs rs → r ∈ rs → Cost (fst (snd r))
  lookup (cons k ks) here = k
  lookup (cons k ks) (there m) = lookup ks m
  Cell : List A → Set
  Cell xs = Σ (T.Cell xs) λ u → Cost (fst u)
  append : ∀ {xs ys} → Cell xs → (op : Code) → run xs (op ∷ []) ≡ just ys → Cell ys
  append ((ps , valid) , cached n e) op legal = ((ps ++ (op ∷ [])) , (resume [] ps (op ∷ []) valid ∙ legal)) ,
    cached _ (C.Entry.exact (C.push (C.entry ps n e) op))
  choose : ∀ {ys} → Cell ys → Cell ys → Cell ys
  choose (u , a) (v , b) with compare (value a) (value b)
  ... | inl _ = u , a
  ... | inr _ = v , b
  agreement : ∀ {ys} (x y : Cell ys) → fst (choose x y) ≡ T.choose (fst x) (fst y)
  agreement (u , cached ._ refl) (v , cached ._ refl) with compare (price (fst u)) (price (fst v))
  ... | inl _ = refl
  ... | inr _ = refl

  module Step (ys : List A) where
    open Scan eq? target c p ys
    reduce : ∀ rs → Costs rs → Cell ys → Cell ys
    reduce rs ks lit with longest rs
    ... | none _ = lit
    ... | won (hit (xs , u) i k legal) (m , _) _ = choose (append (u , lookup ks m) (ptr i k) legal) lit
    same : ∀ rs ks lit → fst (reduce rs ks lit) ≡ R.Step.reduce ys rs (fst lit)
    same rs ks lit with longest rs
    ... | none _ = refl
    ... | won (hit (xs , u) i k legal) (m , _) _ = agreement (append (u , lookup ks m) (ptr i k) legal) lit

  cast : ∀ {xs ys} → xs ≡ ys → Cell xs → Cell ys
  cast refl u = u
  forget-cast : ∀ {xs ys} (e : xs ≡ ys) (u : Cell xs) → fst (cast e u) ≡ T.substCell e (fst u)
  forget-cast refl u = refl

  literal : ∀ {xs} → Cell xs → (a : A) → Cell (xs ++ (a ∷ []))
  literal ((ps , ok) , cached n exact) a = ((ps ++ (sym a ∷ [])) , resume [] ps (sym a ∷ []) ok) ,
    cached _ (C.Entry.exact (C.push (C.entry ps n exact) (sym a)))

  fill : ∀ xs → Cell xs → ∀ rs → Costs rs → (rest : List A) → Cell (xs ++ rest)
  fill xs ((ps , ok) , n) rs ks [] = (ps , (ok ∙ prefix-law xs [])) , n
  fill xs u rs ks (a ∷ rest) = cast (assoc xs (a ∷ []) rest) (fill ys next hist saved rest)
    where ys = xs ++ (a ∷ [])
          hist = (xs , fst u) ∷ rs
          saved = cons (snd u) ks
          next = Step.reduce ys hist saved (literal u a)

  -- Erasing cached prices commutes with the complete prefix loop.
  simulate : ∀ xs u rs ks rest → fst (fill xs u rs ks rest) ≡ R.fill xs (fst u) rs rest
  simulate xs ((ps , ok) , n) rs ks [] = refl
  simulate xs u rs ks (a ∷ rest) = begin
    fst (cast e (fill ys next hist saved rest))        ≡⟨ forget-cast e _ ⟩
    T.substCell e (fst (fill ys next hist saved rest)) ≡⟨ cong (T.substCell e) (simulate ys next hist saved rest) ⟩
    T.substCell e (R.fill ys (fst next) hist rest)     ≡⟨ cong (λ v → T.substCell e (R.fill ys v hist rest)) (Step.same ys hist saved (literal u a)) ⟩
    R.fill xs (fst u) rs (a ∷ rest) ∎
    where ys = xs ++ (a ∷ [])
          hist = (xs , fst u) ∷ rs
          saved = cons (snd u) ks
          next = Step.reduce ys hist saved (literal u a)
          e = assoc xs (a ∷ []) rest

  start : Cell []
  start = ([] , refl) , cached 0 refl
  encode = fill [] start [] nil target
  agrees : fst encode ≡ R.encode
  agrees = simulate [] start [] nil target

  -- Read the cached number as the price of the reference encoder,
  -- then apply its bound to an arbitrary decoding of the same target.
  optimum-price : value (snd encode) ≡ price (fst R.encode)
  optimum-price = begin
    value (snd encode)       ≡⟨ exact (snd encode) ⟩
    price (fst (fst encode)) ≡⟨ cong (λ u → price (fst u)) agrees ⟩
    price (fst R.encode)     ∎
  minimum : ∀ ps → run [] ps ≡ just target → value (snd encode) ≤ price ps
  minimum ps valid rewrite optimum-price = Optimal.Solver.minimum eq? target c p ps valid
