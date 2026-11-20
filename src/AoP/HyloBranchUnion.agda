{-# OPTIONS --safe --without-K #-}
module AoP.HyloBranchUnion where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (_⊔_)
open import AoP.RelationalSums using (_⊕_; left; right)
open import AoP.CopairCancellation using (copair)

-- §6.3, Corollary 6.1 in Rel. The producer chooses a tagged layer.
-- Recursive processing by a sum lifting preserves that tag, so it is
-- impossible for the consumer to recombine at the other branch.
module Step {A B C D E F : Set} (r : A ← C) (t : A ← D)
  (s : B ← E) (u : B ← F) (g : C ← E) (h : D ← F) where
  joint = (copair r t ∘ (g ⊕ h)) ∘ copair s u ˘
  branches = ((r ∘ g) ∘ s ˘) ⊔ ((t ∘ h) ∘ u ˘)

  split : joint ⊆ branches
  split (inl e , (. (inl _) , r′ , left g′) , s′) = inl (e , (_ , r′ , g′) , s′)
  split (inr f , (. (inr _) , t′ , right h′) , u′) = inr (f , (_ , t′ , h′) , u′)
  join : branches ⊆ joint
  join (inl (e , (c , r′ , g′) , s′)) = inl e , (inl c , r′ , left g′) , s′
  join (inr (f , (d , t′ , h′) , u′)) = inr f , (inr d , t′ , right h′) , u′

-- Instantiate the calculation at *each* recursive candidate. Transport
-- both fixedness and leastness; equality at the solution alone would
-- not justify reusing the induction rule for all other candidates.
module Least {A B C D E F : Set} (r : A ← C) (t : A ← D) (s : B ← E) (u : B ← F)
  (G : A ← B → C ← E) (H : A ← B → D ← F) where
  module At (x : A ← B) = Step r t s u (G x) (H x)
  module From (l : A ← B) (roll : At.joint l ⊆ l) (unroll : l ⊆ At.joint l)
    (least : ∀ x → At.joint x ⊆ x → l ⊆ x) where
    fold : At.branches l ⊆ l
    fold p = roll (At.join l p)
    unfold : l ⊆ At.branches l
    unfold p = At.split l (unroll p)
    induction : ∀ x → At.branches x ⊆ x → l ⊆ x
    induction x pre = least x (λ p → pre (At.split x p))
