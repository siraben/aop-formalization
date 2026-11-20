{-# OPTIONS --safe --without-K #-}
module AoP.Party where

open import AoP.Prelude
open import AoP.Trees using (Rose; Forest; fork; null; grow)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool

-- §7.3. A plan is indexed by the actual hierarchy and by whether the
-- immediate supervisor attends. Its constructors enforce feasibility.
module Planning {Employee Score : Set} (rating : Employee → Score)
  (zero : Score) (_+_ : Score → Score → Score) (_≤_ : Score → Score → Set)
  (refl≤ : ∀ x → x ≤ x) (trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z)
  (mono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d))
  (compare : ∀ x y → (x ≤ y) ⊎ (y ≤ x)) where

  mutual
    data Plan : Bool → Rose Employee → Set where
      invite : ∀ {e ts} → Guests true ts → Plan false (fork e ts)
      omit : ∀ {p e ts} → Guests false ts → Plan p (fork e ts)
    data Guests (p : Bool) : Forest Employee → Set where
      none : Guests p null
      join : ∀ {t ts} → Plan p t → Guests p ts → Guests p (grow t ts)

  mutual
    score : ∀ {p t} → Plan p t → Score
    score (invite {e} g) = rating e + total g
    score (omit g) = total g
    total : ∀ {p ts} → Guests p ts → Score
    total none = zero
    total (join t ts) = score t + total ts

  -- Carry a feasible guest list together with its upper-bound proof.
  Best : ∀ {P : Set} → (P → Score) → Set
  Best {P} f = Σ P λ p → ∀ q → f q ≤ f p

  choose : ∀ {t} → Best (total {true} {t}) → Best (total {false} {t}) →
           ∀ e → Best (score {false} {fork e t})
  choose (ins , imax) (outs , omax) e with compare (rating e + total ins) (total outs)
  ... | inl lose = omit outs , λ where
    (omit g) → omax g
    (invite g) → trans (mono (refl≤ _) (imax g)) lose
  ... | inr win = invite ins , λ where
    (omit g) → trans (omax g) win
    (invite g) → mono (refl≤ _) (imax g)

  -- Compute the two supervisor states together, sharing the child table.
  mutual
    tree : ∀ t → Best (score {true} {t}) × Best (score {false} {t})
    tree (fork e ts) with forest ts
    ... | ins , (outs , omax) = (omit outs , (λ { (omit g) → omax g })) , choose ins (outs , omax) e
    forest : ∀ ts → Best (total {true} {ts}) × Best (total {false} {ts})
    forest null = (none , (λ { none → refl≤ zero })) , (none , (λ { none → refl≤ zero }))
    forest (grow t ts) with tree t | forest ts
    ... | (a , ma) , (b , mb) | (as , mas) , (bs , mbs) =
      (join a as , (λ { (join x xs) → mono (ma x) (mas xs) })) ,
      (join b bs , (λ { (join x xs) → mono (mb x) (mbs xs) }))
