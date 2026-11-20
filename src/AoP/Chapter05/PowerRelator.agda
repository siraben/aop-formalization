{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PowerRelator where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (ℙ; _≐_)
open import AoP.Chapter04.Shunting using (Id)
private variable A B C : Set

-- §5.4. Unlike the existential image, the power relator does not select
-- a unique output set. It requires coverage in both directions.
record Lift (R : B ← A) (Y : ℙ B) (X : ℙ A) : Set where
  constructor cover
  field
    backward : ∀ b → Y b → Σ _ λ a → X a × R b a
    forward  : ∀ a → X a → Σ _ λ b → Y b × R b a
open Lift

flip : (R : B ← A) (Y : ℙ B) (X : ℙ A) → Lift R Y X → Lift (R ˘) X Y
flip R Y X p = cover (forward p) (backward p)

identity : (X Y : ℙ A) → Lift Id Y X → Y ≐ X
identity X Y p = (λ b y → transport (backward p b y)) , (λ a x → transport′ (forward p a x))
  where
  transport : ∀ {b} → Σ _ (λ a → X a × (b ≡ a)) → X b
  transport (_ , x , refl) = x
  transport′ : ∀ {a} → Σ _ (λ b → Y b × (b ≡ a)) → Y a
  transport′ (_ , y , refl) = y

identity′ : (X Y : ℙ A) → Y ≐ X → Lift Id Y X
identity′ X Y (l , r) = cover (λ b y → b , l b y , refl) (λ a x → a , r a x , refl)

module Composition (S : C ← B) (R : B ← A) (Z : ℙ C) (X : ℙ A) where
  compose : (Y : ℙ B) → Lift S Z Y → Lift R Y X → Lift (S ∘ R) Z X
  backward (compose Y s r) c z =
    let b , y , sb = backward s c z; a , x , ra = backward r b y
    in a , x , b , sb , ra
  forward (compose Y s r) a x =
    let b , y , ra = forward r a x; c , z , sb = forward s b y
    in c , z , b , sb , ra

  -- For the reverse inclusion, take *all* middle points on paths from X
  -- to Z. No global choice of representatives is necessary.
  Middle : ℙ B
  Middle b = (Σ _ λ c → Z c × S c b) × (Σ _ λ a → X a × R b a)

  factor : Lift (S ∘ R) Z X → Lift S Z Middle × Lift R Middle X
  backward (fst (factor p)) c z =
    let a , x , b , s , r = backward p c z in b , ((c , z , s) , (a , x , r)) , s
  forward (fst (factor p)) b ((c , z , s) , _) = c , z , s
  backward (snd (factor p)) b (_ , (a , x , r)) = a , x , r
  forward (snd (factor p)) a x =
    let c , z , b , s , r = forward p a x in b , ((c , z , s) , (a , x , r)) , r
