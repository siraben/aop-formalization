{-# OPTIONS --safe --without-K #-}
module AoP.DisjointPowerMinimum where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.RelationalSums using (_⊕_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Thinning using (Pred; Thin; Min)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.Power using (_≐_)
open import AoP.Complement using (⊥)
import AoP.DisjointMinimum as Image
import AoP.DisjointFibres as Fib
import AoP.TaggedThinning as Tag

-- Proposition 9.1 with the relational power P: an outcome set may
-- select among several outcomes, but must cover every retained input.
module At {A B C D : Set} (V : C ← A) (W : C ← B) (U : D ← A) (Z : D ← B)
          (Q : A ← A) (S : B ← B) (R : D ← D) where
  open Image.At V W U Z Q S R using (evaluate; module SelectBranch)
  open Tag.Law Q S renaming (R to TagR)
  open Fib.Law V W
  Body : ∀ {I} → I ← I → D ← I → Pred I → D → Set₁
  Body T E X d = Σ (Pred _) λ Y → Σ (Pred D) λ O → Thin T Y X × Lift E O Y × Min R d O
  narrowL : ∀ {P O} → P ≐ L (λ a → P (inl a)) → Lift evaluate O P → Lift U O (λ a → P (inl a))
  narrowL eq p = cover back (λ a → Lift.forward p (inl a))
    where back : ∀ d → _ → _
          back d o with Lift.backward p d o
          ... | inl a , y , u = a , y , u
          ... | inr b , y , z with fst eq (inr b) y
          ... | ()
  narrowR : ∀ {P O} → P ≐ TagR (λ b → P (inr b)) → Lift evaluate O P → Lift Z O (λ b → P (inr b))
  narrowR eq p = cover back (λ b → Lift.forward p (inr b))
    where back : ∀ d → _ → _
          back d o with Lift.backward p d o
          ... | inr b , y , z = b , y , z
          ... | inl a , y , u with fst eq (inl a) y
          ... | ()
  widenL : ∀ {X O} → Lift U O X → Lift evaluate O (L X)
  widenL p = cover (λ d o → let a , x , u = Lift.backward p d o in inl a , x , u)
                   (λ { (inl a) → Lift.forward p a ; (inr b) () })
  widenR : ∀ {X O} → Lift Z O X → Lift evaluate O (TagR X)
  widenR p = cover (λ d o → let b , x , z = Lift.backward p d o in inr b , x , z)
                   (λ { (inr b) → Lift.forward p b ; (inl a) () })

  module Branch (dis : Disjoint) (test : ∀ c → Left c ⊎ (Left c → ⊥)) where
    open SelectBranch dis test using (left-eq; right-eq)
    side : C → D → Set₁
    side c d with test c
    ... | inl _ = Body Q U (V c) d
    ... | inr _ = Body S Z (W c) d
    change : ∀ {I} {T : I ← I} {X Y P} → X ≐ Y → Thin T P X → Thin T P Y
    change eq t = AoP.Thinning.thin (λ {i} p → fst eq i (Thin.subset t p)) (λ i y → Thin.cover t i (snd eq i y))
    project : ∀ c d → Body (Q ⊕ S) evaluate (fibre c) d → side c d
    project c d (P , O , t , p , m) with test c
    ... | inl yes = _ , O , lower (V c) P t′ , narrowL (shape (V c) P t′) p , m
      where t′ = change (left-eq c yes) t
    ... | inr no = _ , O , lower-right (W c) P t′ , narrowR (shape-right (W c) P t′) p , m
      where t′ = change (right-eq c no) t
    inject : ∀ c d → side c d → Body (Q ⊕ S) evaluate (fibre c) d
    inject c d v with test c | v
    ... | inl yes | P , O , t , p , m = _ , O , change (snd eq , fst eq) (lift t) , widenL p , m
      where eq = left-eq c yes
    ... | inr no | P , O , t , p , m = _ , O , change (snd eq , fst eq) (lift-right t) , widenR p , m
      where eq = right-eq c no
