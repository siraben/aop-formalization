{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DistributedCase where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.Products using ([_,_])
open import AoP.Chapter03.Conditions using (distr; undistr; cancel)
private variable A B C D E F : Set

-- Exercise 3.28 in Fun. A case analysis on one component of a pair
-- can instead branch on the whole pair after distribution. For the
-- calculation, first check the two injections, then insert undistr
-- after distr using their cancellation law.
cross : (A → D) → (B → E) → A × B → D × E
cross f g (a , b) = f a , g b

branches : (f : A → D) (g : B → F) (h : C → F) (s : (A × B) ⊎ (A × C)) →
           cross f [ g , h ] (undistr s) ≡ [ cross f g , cross f h ] s
branches f g h (inl _) = refl
branches f g h (inr _) = refl

law : (f : A → D) (g : B → F) (h : C → F) (p : A × (B ⊎ C)) →
      cross f [ g , h ] p ≡ [ cross f g , cross f h ] (distr p)
law f g h p = begin
  cross f [ g , h ] p ≡⟨ cong (cross f [ g , h ]) (back (cancel p)) ⟩
  cross f [ g , h ] (undistr (distr p)) ≡⟨ branches f g h (distr p) ⟩
  [ cross f g , cross f h ] (distr p) ∎
  where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
        back refl = refl
