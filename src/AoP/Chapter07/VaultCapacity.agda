{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VaultCapacity where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
import AoP.Chapter07.ReserveTransfer as T
open import AoP.Chapter07.ReserveExtrema using (summary; Needs)
open import AoP.Common.NatOrder using (_≤_; s≤; z≤; rid; chain; sum-mono)
open import AoP.Chapter08.ParagraphMinimum using (Dec; le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Stock plus empty space is invariant under transfers. With the total
-- bounded by capacity we can forget the empty account and obtain an
-- ordinary bank run. Conversely the actual unused capacity reconstructs
-- that account uniquely at every step.
private
  back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  back refl = refl
  plus-suc : ∀ r s → r + suc s ≡ suc (r + s)
  plus-suc zero s = refl
  plus-suc (suc r) s = cong suc (plus-suc r s)
  move : ∀ n r s → r + (n + s) ≡ (n + r) + s
  move zero r s = refl
  move (suc n) r s = plus-suc r (n + s) ∙ cong suc (move n r s)
  left : ∀ r s → r ≤ r + s
  left zero s = z≤
  left (suc r) s = s≤ (left r s)
  cancel : ∀ r {a b} → r + a ≤ r + b → a ≤ b
  cancel zero p = p
  cancel (suc r) (s≤ p) = cancel r p
  gap : ∀ {r cap} → r ≤ cap → Σ Nat λ s → cap ≡ r + s
  gap z≤ = _ , refl
  gap (s≤ p) with gap p
  ... | s , refl = s , refl
  change : ∀ {a b cap} → a ≡ b → a ≤ cap → b ≤ cap
  change refl p = p

module Vault (cap : Nat) where
  open Bank cap
  forget : ∀ {ts r s} → T.Executes ts r s → r + s ≤ cap → Σ Nat λ c → Run ts r c
  forget (T.stop {r} {s}) fits = _ , stop (chain (left r s) fits)
  forget (T.credit n r s p) fits with forget p (change (move n r s) fits)
  ... | c , tail = c , post (chain (left r _) fits) (credit n r) tail
  forget (T.debit n r s p) fits with forget p (change (back (move n r s)) fits)
  ... | c , tail = c , post (chain (left (n + r) _) fits) (debit n r) tail

  start : ∀ {ts r c} → Run ts r c → r ≤ cap
  start (stop p) = p
  start (post p _ _) = p

  restore : ∀ {ts r c} → Run ts r c → ∀ s → cap ≡ r + s → T.Executes ts r s
  restore (stop _) s eq = T.stop
  restore (post fits (debit n r) p) s eq = T.debit n r s (restore p (n + s) (eq ∙ back (move n r s)))
  restore (post fits (credit n r) p) s eq with gap (start p)
  ... | d , cap-eq with cancel-eq r (back eq ∙ cap-eq ∙ back (move n r d))
    where
    cancel-eq : ∀ r {a b} → r + a ≡ r + b → a ≡ b
    cancel-eq zero e = e
    cancel-eq (suc r) e = cancel-eq r (cong pred e)
      where pred : Nat → Nat
            pred zero = zero
            pred (suc x) = x
  ...   | refl = T.credit n r d (restore p d cap-eq)

  enough : ∀ ts → T.minimum-capacity ts ≤ cap → Secure ts
  enough ts fits = _ , forget (T.attained ts) fits

  required : ∀ ts → Secure ts → T.minimum-capacity ts ≤ cap
  required ts (r , c , run) with gap (start run)
  ... | s , eq = change-total eq (T.least (restore run s eq))
    where change-total : ∀ {a b c} → c ≡ b → a ≤ b → a ≤ c
          change-total refl p = p

  fast? : ∀ ts → Dec (Secure ts)
  fast? ts with le? (T.minimum-capacity ts) cap
  ... | inl fits = inl (enough ts fits)
  ... | inr no = inr λ secure → no (required ts secure)
