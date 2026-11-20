{-# OPTIONS --safe --without-K #-}
module AoP.ParagraphSnocWaste where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.ParagraphSnocStep using (module Step; State)
open import AoP.ParagraphSnocFold using (module Layout)
open import AoP.ParagraphAllowanceOrder using (module Law)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (assoc; swap; unit; sym; move)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

module Objective (m a : Nat) (fit : a ≤ m) where
  open Layout m a fit
  open Step m using (glue; line)
  open Law m
  flat : Snoc Nat → Nat
  flat ε = a
  flat (ws ▻ w) = suc w + flat ws
  waste : ∀ {ws s} → History ws s → Nat
  waste start = 0
  waste (append h (glue _)) = waste h
  waste (append {s = k , l} h (line _)) = (m - l) + waste h
  fits : ∀ {ws s} → History ws s → snd s ≤ m
  fits start = fit
  fits (append h (glue p)) = p
  fits (append h (line p)) = p
  private
    fill : ∀ l m → l ≤ m → (m - l) + l ≡ m
    fill 0 m p = unit m
    fill (suc l) (suc m) (s≤ p) = move (m - l) l ∙ cong suc (fill l m p)
    plus-comm : ∀ x y → x + y ≡ y + x
    plus-comm x y = sym (cong (x +_) (unit y)) ∙ swap x y 0 ∙ cong (y +_) (unit x)
    rotate : ∀ d w n l → d + (suc w + (n + l)) ≡ (suc (d + l) + n) + w
    rotate d w n l = cong (d +_) (swap (suc w) n l) ∙ swap d n (suc w + l) ∙
      cong (n +_) (cong (d +_) (cong suc (plus-comm w l)) ∙ move d (l + w) ∙ cong suc (sym (assoc d l w))) ∙
      swap n (suc (d + l)) w ∙ sym (assoc (suc (d + l)) n w)

  balance : ∀ {ws s} (h : History ws s) → waste h + flat ws ≡ total s
  balance start = refl
  balance (append {ws} {k , l} {w} h (glue p)) = swap (waste h) (suc w) (flat ws) ∙ cong (suc w +_) (balance h) ∙ swap (suc w) _ l ∙ cong ((k * suc m) +_) (sym (move w l))
  balance (append {ws} {k , l} {w} h (line p)) = assoc (m - l) (waste h) _ ∙ cong ((m - l) +_) (swap (waste h) (suc w) (flat ws) ∙ cong (suc w +_) (balance h)) ∙ rotate (m - l) w _ l ∙ cong (λ v → (suc v + k * suc m) + w) (fill l m (fits h))

  minimum : ∀ {ws s} (h : History ws s) → Σ (History ws (layout ws)) λ g → waste g ≤ waste h
  minimum {ws} h with certified h
  ... | g , adv = g , waste-order (flat ws) (waste g) (waste h) _ _ (balance g) (balance h) (fits g) adv
