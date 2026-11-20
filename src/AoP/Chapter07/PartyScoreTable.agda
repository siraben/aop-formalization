{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyScoreTable where

open import AoP.Common.Prelude
open import Agda.Builtin.Bool using (true; false)
open import AoP.Chapter01.Trees using (Rose; Forest; fork; grow; null)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter07.Party using (module Planning)

-- §7.3. Cache both scores instead of rescanning the selected plans
-- to compare the invite and omit options. The first entry applies
-- when the parent attends; the second applies when it stays home.
module Law {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Planning rating z add R rid tr mono cmp
  better : S → S → S
  better x y with cmp x y
  ... | inl _ = y
  ... | inr _ = x
  mutual
    scores : Rose E → S × S
    scores (fork e ts) with totals ts
    ... | i , o = o , better (add (rating e) i) o
    totals : Forest E → S × S
    totals null = z , z
    totals (grow t ts) with scores t | totals ts
    ... | i , o | is , os = add i is , add o os

  choice : ∀ {ts} e (i : Best (total {true} {ts})) (o : Best (total {false} {ts})) →
    score (fst (choose i o e)) ≡ better (add (rating e) (total (fst i))) (total (fst o))
  choice e (g , ig) (h , oh) with cmp (add (rating e) (total g)) (total h)
  ... | inl _ = refl
  ... | inr _ = refl

  mutual
    correct : ∀ t → (score (fst (fst (tree t))) , score (fst (snd (tree t)))) ≡ scores t
    correct (fork e ts) with forest ts | totals ts | correctᶠ ts
    ... | i , (g , opt) | _ | refl rewrite choice e i (g , opt) = refl
    correctᶠ : ∀ ts → (total (fst (fst (forest ts))) , total (fst (snd (forest ts)))) ≡ totals ts
    correctᶠ null = refl
    correctᶠ (grow t ts) with tree t | scores t | correct t | forest ts | totals ts | correctᶠ ts
    ... | _ | _ | refl | _ | _ | refl = refl
