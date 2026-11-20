{-# OPTIONS --safe --without-K #-}
module AoP.LatenessOptimal where

open import AoP.Prelude
open import AoP.SignedLateness using (Peak; bottom; finite; raise; score)
open import AoP.SignedSegment using (_≤_; cmp; rid)
open import AoP.LatenessPeakBound using (Below; module Bound)
import AoP.LatenessThreshold as Threshold
open import AoP.LatenessSchedule using (Run; stop; choose; schedule; permutation)
open import AoP.Tardiness using (Job)
open import AoP.Snoc using (Snoc; ε; _▻_; append)
open import AoP.Permutations using (Perm; insert)
open import AoP.Polynomial using (inl; inr)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Int using (Int)

_≼_ : Peak → Peak → Set
bottom ≼ _ = ⊤
finite _ ≼ bottom = ⊥
finite a ≼ finite b = a ≤ b
peak : List Job → Peak
peak xs = score (append ε xs)

private
  realized : ∀ p q → Σ Int λ k → raise p q ≡ finite k
  realized bottom q = q , refl
  realized (finite p) q with cmp p q
  ... | inl _ = q , refl
  ... | inr _ = p , refl
  nonempty : ∀ p j js → Σ Int λ k → score (append (p ▻ j) js) ≡ finite k
  nonempty p j [] = realized (score p) _
  nonempty p j (x ∷ xs) = nonempty (p ▻ j) x xs
  self : ∀ p k → p ≡ finite k → Below p k
  self .(finite k) k refl = rid k
  lower : ∀ p k → Below p k → p ≼ finite k
  lower bottom k _ = tt
  lower (finite p) k le = le

-- Use the competitor's own peak as the threshold. Only the empty
-- case has no finite peak, and its greedy schedule is empty as well.
optimal : ∀ {js out ys} → Run js out → Perm js ys → peak out ≼ peak ys
optimal stop perm = tt
optimal {ys = []} (choose j js p r) (insert perm ())
optimal {out = out} {y ∷ ys} run perm with nonempty ε y ys
... | k , eq = transport eq (lower (peak out) k (Bound.collect k ε out tt
  (Threshold.Bound.transport k run perm (snd (Bound.expose k ε (y ∷ ys) (self _ k eq))))))
  where transport : ∀ {p} → p ≡ finite k → peak out ≼ finite k → peak out ≼ p
        transport refl le = le

certified : ∀ js → Σ (List Job) λ out → Perm js out × (∀ ys → Perm js ys → peak out ≼ peak ys)
certified js with schedule js
... | out , run = out , permutation run , λ ys perm → optimal run perm
