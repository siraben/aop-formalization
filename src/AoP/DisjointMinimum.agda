{-# OPTIONS --safe --without-K #-}
module AoP.DisjointMinimum where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.RelationalSums using (_⊕_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Thinning using (Pred; Thin; thin; Min)
open import AoP.Complement using (⊥)
open import AoP.Power using (_≐_)
open import AoP.TaggedThinning using (module Law)
import AoP.DisjointFibres as Fib

-- Proposition 9.1. At a given input, evaluate the retained alternatives
-- and minimize their outcomes. Disjoint ranges allow the whole operation
-- to run on just one side of the sum, even outside both ranges.
module At {A B C D : Set} (V : C ← A) (W : C ← B) (U : D ← A) (Z : D ← B)
          (Q : A ← A) (S : B ← B) (R : D ← D) where
  open Law Q S renaming (R to R′)
  open Fib.Law V W
  evaluate : D ← (A ⊎ B)
  evaluate d (inl a) = U d a
  evaluate d (inr b) = Z d b
  Image : ∀ {I} → D ← I → Pred I → Pred D
  Image E X d = Σ _ λ i → X i × E d i
  Solve : ∀ {I} → I ← I → D ← I → Pred I → D → Set₁
  Solve T E X d = Σ (Pred _) λ Y → Thin T Y X × Min R d (Image E Y)
  private
    change : ∀ {I} {T : I ← I} {X Y P} → X ≐ Y → Thin T P X → Thin T P Y
    change eq t = thin (λ {i} p → fst eq i (Thin.subset t p)) (λ i y → Thin.cover t i (snd eq i y))
    transport : ∀ {X Y d} → X ≐ Y → Min R d X → Min R d Y
    transport eq (x , best) = fst eq _ x , λ y p → best y (snd eq y p)
    imagesL : ∀ P → Image evaluate (L P) ≐ Image U P
    imagesL P = (λ { d (inl a , p , u) → a , p , u }) , λ { d (a , p , u) → inl a , p , u }
    imagesR : ∀ P → Image evaluate (R′ P) ≐ Image Z P
    imagesR P = (λ { d (inr b , p , z) → b , p , z }) , λ { d (b , p , z) → inr b , p , z }
    map-image : ∀ {P P′} → P ≐ P′ → Image evaluate P ≐ Image evaluate P′
    map-image eq = (λ { d (i , p , u) → i , fst eq i p , u }) , λ { d (i , p , u) → i , snd eq i p , u }

  module SelectBranch (dis : Disjoint) (test : ∀ c → Left c ⊎ (Left c → ⊥)) where
    left-eq : ∀ c → Left c → fibre c ≐ L (V c)
    left-eq c yes = (λ { (inl a) v → v ; (inr b) w → dis c yes (b , w) }) , λ { (inl a) v → v ; (inr b) () }
    right-eq : ∀ c → (Left c → ⊥) → fibre c ≐ R′ (W c)
    right-eq c no = (λ { (inl a) v → no (a , v) ; (inr b) w → w }) , λ { (inl a) () ; (inr b) w → w }
    Whole = Solve (Q ⊕ S) evaluate
    Choice : C → D → Set₁
    Choice c d with test c
    ... | inl _ = Solve Q U (V c) d
    ... | inr _ = Solve S Z (W c) d
    forward : ∀ c d → Whole (fibre c) d → Choice c d
    forward c d (P , t , m) with test c
    ... | inl yes = _ , lower (V c) P t′ , transport (imagesL _) (transport (map-image (shape (V c) P t′)) m)
      where t′ = change (left-eq c yes) t
    ... | inr no = _ , lower-right (W c) P t′ , transport (imagesR _) (transport (map-image (shape-right (W c) P t′)) m)
      where t′ = change (right-eq c no) t
    backward : ∀ c d → Choice c d → Whole (fibre c) d
    backward c d v with test c | v
    ... | inl yes | P , t , m = _ , change (snd (left-eq c yes) , fst (left-eq c yes)) (lift t) , transport (snd (imagesL P) , fst (imagesL P)) m
    ... | inr no | P , t , m = _ , change (snd (right-eq c no) , fst (right-eq c no)) (lift-right t) , transport (snd (imagesR P) , fst (imagesR P)) m
