{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.UnzipOneSide where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Shunting using (graph; Id)
import AoP.Chapter05.UnzipProjectionLaw as Forward

module Law (F : Set → Set) (L : ∀ {A B} → B ← A → F B ← F A)
  (map : ∀ {A B} → (A → B) → F A → F B)
  (intro : ∀ {A B} (f : A → B) → graph (map f) ⊆ L (graph f))
  (elim : ∀ {A B} (f : A → B) → L (graph f) ⊆ graph (map f))
  (mono : ∀ {A B} (P Q : B ← A) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {A B C} (P : C ← B) (Q : B ← A) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {A B C} (P : C ← B) (Q : B ← A) → L (P ∘ Q) ⊆ L P ∘ L Q)
  (identity : ∀ {A} → L (Id {A}) ⊆ Id) where
  open Forward.Law F L map intro elim mono join split
  -- Move only the left coordinate. Compose P with the first projection,
  -- factor through pairs, then split the lifted composite. Projecting
  -- the resulting witness to the right gives equality by identity.
  left : ∀ {A B C} (P : C ← A) (u : F (A × B)) v → L P v (map fst u) →
    Σ (F (C × B)) λ z → L (tensor P Id) z u × ((map fst z ≡ v) × (map snd z ≡ map snd u))
  left {B = B} P u v p with split (graph fst) (tensor P Id) (mono (P ∘ graph fst) (graph fst ∘ tensor P (Id {B})) factor
                                  (join P (graph fst) (_ , p , intro fst refl)))
    where factor : P ∘ graph fst ⊆ graph fst ∘ tensor P (Id {B})
          factor {a = a , b} (_ , r , refl) = (_ , b) , refl , r , refl
  ... | z , f , rel = z , rel , elim fst f , identity (project snd snd (tensor P Id) Id snd rel)
  right : ∀ {A B D} (Q : D ← B) (u : F (A × B)) v → L Q v (map snd u) →
    Σ (F (A × D)) λ z → L (tensor Id Q) z u × ((map fst z ≡ map fst u) × (map snd z ≡ v))
  right {A} Q u v q with split (graph snd) (tensor Id Q) (mono (Q ∘ graph snd) (graph snd ∘ tensor (Id {A}) Q) factor
                                  (join Q (graph snd) (_ , q , intro snd refl)))
    where factor : Q ∘ graph snd ⊆ graph snd ∘ tensor (Id {A}) Q
          factor {a = a , b} (_ , r , refl) = (a , _) , refl , refl , r
  ... | z , f , rel = z , rel , identity (project fst fst (tensor Id Q) Id fst rel) , elim snd f

  backward : ∀ {A B C D} (P : C ← A) (Q : D ← B) → tensor (L P) (L Q) ∘ graph unzip ⊆ graph unzip ∘ L (tensor P Q)
  backward P Q {a = u} (_ , (p , q) , refl) with left P u _ p
  ... | z , l , refl , same with right Q z _ (transport same q)
    where transport : ∀ {x y v} → x ≡ y → L Q v y → L Q v x
          transport refl r = r
  ... | w , r , eq , refl = w , cong (λ x → x , map snd w) eq , mono (tensor Id Q ∘ tensor P Id) (tensor P Q) combine (join (tensor Id Q) (tensor P Id) (z , r , l))
    where combine : tensor Id Q ∘ tensor P Id ⊆ tensor P Q
          combine (_ , (refl , q′) , p′ , refl) = p′ , q′
