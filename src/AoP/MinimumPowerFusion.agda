{-# OPTIONS --safe --without-K #-}
module AoP.MinimumPowerFusion where

open import AoP.Prelude
open import AoP.Power using (ℙ; ℰ)
open import AoP.Relations using (_←_)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.Thinning using (Min)

-- §7.1 (7.9–10). The power relator may select fewer outputs than
-- the full image, provided its selection still covers every input.
module Law {A B : Set} (R : B ← B) (S : B ← A) (X : ℙ A) where
  Chosen : B → Set₁
  Chosen b = Σ (ℙ B) λ Y → Min R b Y × Lift S Y X
  Test : B → Set
  Test b = ℰ S X b × (∀ a → X a → Σ B λ c → S c a × R b c)

  -- Read the preimage of the minimum, then use forward coverage to
  -- find one output per input against which it wins.
  forward : ∀ {b} → Chosen b → Test b
  forward {b} (Y , (yb , wins) , cov) with Lift.backward cov b yb
  ... | a , x , s = (a , s , x) , rivals
    where rivals : ∀ i → X i → Σ B λ c → S c i × R b c
          rivals i input with Lift.forward cov i input
          ... | c , y , sc = c , sc , wins c y

  -- Every selected minimum must also beat itself. Keeping this local
  -- test gives an exact characterization even for a strict comparison.
  diagonal : ∀ {b} → Chosen b → R b b
  diagonal {b} (Y , (member , wins) , cov) = wins b member

  -- Reconstruct a single suitable set: all image elements that b
  -- beats. The per-input tests ensure coverage, while reflexivity at
  -- b itself is what admits the chosen minimum to this set.
  backward : ∀ {b} → R b b → Test b → Chosen b
  backward {b} self (present , rivals) = Y , ((present , self) , (λ c → snd)) , cover back forth
    where
      Y : ℙ B
      Y c = ℰ S X c × R b c
      back : ∀ c → Y c → Σ A λ a → X a × S c a
      back c ((a , s , x) , _) = a , x , s
      forth : ∀ a → X a → Σ B λ c → Y c × S c a
      forth a x with rivals a x
      ... | c , sc , bc = c , ((a , sc , x) , bc) , sc
