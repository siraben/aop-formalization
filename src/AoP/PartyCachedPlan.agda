{-# OPTIONS --safe --without-K #-}
module AoP.PartyCachedPlan where

open import AoP.Prelude
open import AoP.Trees using (Rose; Forest; fork; grow; null)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Party using (module Planning)
open import Agda.Builtin.Bool using (true; false)

-- Construct the invitee plan and cache its value in the same pass.
-- The branch decision reads cached fields rather than visiting a plan.
module Law {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Planning rating z add R rid tr mono cmp
  record Entry {X : Set} (value : X → S) : Set where
    constructor entry
    field plan : X
          cached : S
          exact : value plan ≡ cached
          best : ∀ q → R (value q) cached
  open Entry

  select : ∀ e {ts} → Entry (total {true} {ts}) → Entry (total {false} {ts}) → Entry (score {false} {fork e ts})
  select e (entry i a ea ia) (entry o b eb ob) with cmp (add (rating e) a) b
  ... | inl le = entry (omit o) b eb λ where
    (omit g) → ob g
    (invite g) → tr (mono (rid _) (ia g)) le
  ... | inr ge = entry (invite i) _ (cong (add (rating e)) ea) λ where
    (omit g) → tr (ob g) ge
    (invite g) → mono (rid _) (ia g)

  combine : ∀ {p t ts} → Entry (score {p} {t}) → Entry (total {p} {ts}) → Entry (total {p} {grow t ts})
  combine (entry g a ea ga) (entry h b eb hb) = entry (join g h) (add a b)
    (cong (λ x → add x (total h)) ea ∙ cong (add a) eb) λ { (join v vs) → mono (ga v) (hb vs) }
  skip : ∀ e {ts} → Entry (total {false} {ts}) → Entry (score {true} {fork e ts})
  skip e o = entry (omit (plan o)) (cached o) (exact o) (λ { (omit g) → best o g })

  mutual
    table : ∀ t → Entry (score {true} {t}) × Entry (score {false} {t})
    table (fork e ts) with rows ts
    ... | i , o = skip e o , select e i o
    rows : ∀ ts → Entry (total {true} {ts}) × Entry (total {false} {ts})
    rows null = entry none z refl (λ { none → rid z }) , entry none z refl (λ { none → rid z })
    rows (grow t ts) with table t | rows ts
    ... | i , o | is , os = combine i is , combine o os

  guests : Rose E → List E
  guests t = names (plan (snd (table t))) []

  mandatory : ∀ e ts → Entry (λ (g : Guests true ts) → score (invite {e = e} g))
  mandatory e ts with fst (rows ts)
  ... | entry g v eq opt = entry g (add (rating e) v) (cong (add (rating e)) eq)
    (λ q → mono (rid (rating e)) (opt q))

  with-president : E → Forest E → List E
  with-president e ts = e ∷ namesᶠ (plan (mandatory e ts)) []
