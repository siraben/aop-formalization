{-# OPTIONS --safe --without-K #-}
module AoP.Party where

open import AoP.Prelude
open import AoP.Trees using (Rose; Forest; fork; null; grow)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool

-- §7.3 — Who should come to the company party?
--
-- Input: an organisation chart, rooted at the president. In `fork e ts`,
-- e is an employee and ts lists the subtrees of their direct reports.
-- Each employee has a conviviality rating. Return a list of invitees with
-- the greatest possible sum of ratings, subject to one rule: no employee
-- may attend alongside their immediate supervisor. A grandparent and a
-- grandchild may attend together. Ties need not have a unique answer.
--
-- Example: Ada (8) supervises Bo (5) and Cy (5), who have no reports.
-- Inviting Ada scores 8 and rules out both children. Omitting Ada lets
-- both children come, scoring 10. So the answer is [Bo, Cy], unless the
-- president is required to attend, in which case it is [Ada]. Choosing
-- the highest-rated individual first would miss the unconstrained answer.
--
-- Algorithm: solve each subtree under two assumptions about its parent.
-- If the parent attends, the root must stay home. Otherwise compare
-- inviting the root (and forbidding its children) against omitting it
-- (and freeing its children). Sibling subtrees have no constraints between
-- them, so their best scores add. `mono` justifies that last step; `compare`
-- chooses between scores. The score type is abstract so this reasoning
-- does not depend on a particular numeric representation.
--
-- Reading the types: the Boolean in `Plan p t` describes the *parent*,
-- not the employee at t. `Best score` packages a plan with evidence that
-- every competing plan scores at most as much. Start at `invitations` for
-- the ordinary problem or `presidential-invitations` for the variant.
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

  -- The president must attend (second question of §7.3). Do not merely
  -- allow the root to attend: restrict the whole optimization domain to
  -- plans of the form `invite g`. The first forest entry is precisely
  -- the best such g, since its immediate supervisor attends.
  president : ∀ e ts → Best (λ (g : Guests true ts) → score (invite {e = e} g))
  president e ts with fst (forest ts)
  ... | g , optimal = g , λ h → mono (refl≤ (rating e)) (optimal h)

  -- Extract the actual invitation list, not just its score. A forest is
  -- visited left to right, with a suffix accumulator to avoid appends.
  mutual
    names : ∀ {p t} → Plan p t → List Employee → List Employee
    names (invite {e} g) rest = e ∷ namesᶠ g rest
    names (omit g) rest = namesᶠ g rest
    namesᶠ : ∀ {p ts} → Guests p ts → List Employee → List Employee
    namesᶠ none rest = rest
    namesᶠ (join t ts) rest = names t (namesᶠ ts rest)

  invitations : Rose Employee → List Employee
  invitations t = names (fst (snd (tree t))) []

  presidential-invitations : Employee → Forest Employee → List Employee
  presidential-invitations e ts = e ∷ namesᶠ (fst (president e ts)) []
