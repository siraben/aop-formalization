{-# OPTIONS --safe --without-K #-}
module AoP.DPBifunctor where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Shunting using (Id)

-- Proposition 9.4. The first coordinate labels a layer; the second
-- contains subproblems. Lift the two comparisons together to prune
-- whole decompositions. Work backwards from a rival's computed layer.
module Law {K A B : Set} (F : Set → Set → Set)
  (L : ∀ {I J X Y} → J ← I → Y ← X → F J Y ← F I X)
  (mono : ∀ {I J X Y} (P P′ : J ← I) (Q Q′ : Y ← X) → P ⊆ P′ → Q ⊆ Q′ → L P Q ⊆ L P′ Q′)
  (join : ∀ {I J K X Y Z} (P : K ← J) (T : J ← I) (Q : Z ← Y) (S : Y ← X) → L P Q ∘ L T S ⊆ L (P ∘ T) (Q ∘ S))
  (split : ∀ {I J K X Y Z} (P : K ← J) (T : J ← I) (Q : Z ← Y) (S : Y ← X) → L (P ∘ T) (Q ∘ S) ⊆ L P Q ∘ L T S)
  (back : ∀ {I J X Y} (P : J ← I) (Q : Y ← X) → L P Q ˘ ⊆ L (P ˘) (Q ˘))
  (forth : ∀ {I J X Y} (P : J ← I) (Q : Y ← X) → L (P ˘) (Q ˘) ⊆ L P Q ˘)
  (U : K ← K) (V : A ← A) (R : B ← B) (H : B ← A) (h : F K B → B)
  (unit : ∀ k → U k k) (ordered : ∀ {x y} → L U R x y → R (h x) (h y))
  (match : V ∘ H ˘ ⊆ H ˘ ∘ R) where
  monotone : ∀ {x y} → L Id R x y → R (h x) (h y)
  monotone r = ordered (mono Id U R R (λ { refl → unit _ }) (λ x → x) r)
  rotate : U ∘ Id ˘ ⊆ Id ˘ ∘ U
  rotate (_ , u , refl) = _ , refl , u
  prune : ∀ {c b v} → L U V c b → L Id H v b → Σ _ λ w → L Id H w c × R (h w) (h v)
  prune {b = b} q run with split (Id ˘) U (H ˘) R
    (mono (U ∘ Id ˘) (Id ˘ ∘ U) (V ∘ H ˘) (H ˘ ∘ R) rotate match
      (join U (Id ˘) V (H ˘) (b , q , back Id H run)))
  ... | w , feasible , improvement = w , forth Id H feasible , ordered improvement
