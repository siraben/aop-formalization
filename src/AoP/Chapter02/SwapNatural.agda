{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.SwapNatural where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Transformations using (Natural)
open import Agda.Primitive using (lzero; lsuc)

-- Exercise 2.14. Both functors take *two* types and *two* functions.
-- The first builds A × B and the second B × A. For example, swapping
-- (a,b) after applying (f,g) gives (g b,f a), the same pair obtained
-- by swapping first and applying the functions in reverse order.
record Types : Set₁ where
  constructor pair
  field L R : Set
open Types
record Maps (S T : Types) : Set where
  constructor maps
  field left : L S → L T
        right : R S → R T
open Maps

Pairs : Category (lsuc lzero) lzero lzero
Category.Obj Pairs = Types
Category.Hom Pairs = Maps
Category._≈_ Pairs {A} f g = ((a : L A) → left f a ≡ left g a) × ((b : R A) → right f b ≡ right g b)
Category.identity Pairs = maps (λ a → a) (λ b → b)
Category._∘_ Pairs g f = maps (λ a → left g (left f a)) (λ b → right g (right f b))
Category.reflexive Pairs = (λ _ → refl) , (λ _ → refl)
Category.symmetric Pairs (p , q) = Category.symmetric Fun p , Category.symmetric Fun q
Category.transitive Pairs (a , b) (c , d) = (λ x → a x ∙ c x) , (λ y → b y ∙ d y)
Category.compose-cong Pairs {f = f} {g} {s} {t} (a , b) (c , d) =
  (λ x → a (left f x) ∙ cong (left t) (c x)) , (λ y → b (right f y) ∙ cong (right t) (d y))
Category.unitˡ Pairs _ = (λ _ → refl) , (λ _ → refl)
Category.unitʳ Pairs _ = (λ _ → refl) , (λ _ → refl)
Category.assoc Pairs _ _ _ = (λ _ → refl) , (λ _ → refl)

pair-eq : ∀ {A B : Set} {a a′ : A} {b b′ : B} → a ≡ a′ → b ≡ b′ → (a , b) ≡ (a′ , b′)
pair-eq refl refl = refl

LR RL : Functor Pairs Fun
Functor.F₀ LR T = L T × R T
Functor.F₁ LR f (a , b) = left f a , right f b
Functor.resp LR (p , q) (a , b) = pair-eq (p a) (q b)
Functor.identity LR _ = refl
Functor.composition LR _ _ _ = refl
Functor.F₀ RL T = R T × L T
Functor.F₁ RL f (b , a) = right f b , left f a
Functor.resp RL (p , q) (b , a) = pair-eq (q b) (p a)
Functor.identity RL _ = refl
Functor.composition RL _ _ _ = refl

swap : Natural LR RL
Natural.η swap _ (a , b) = b , a
Natural.square swap f (a , b) = refl

unswap : Natural RL LR
Natural.η unswap _ (b , a) = a , b
Natural.square unswap f (b , a) = refl

round-LR : ∀ T x → Natural.η unswap T (Natural.η swap T x) ≡ x
round-LR T (a , b) = refl
round-RL : ∀ T x → Natural.η swap T (Natural.η unswap T x) ≡ x
round-RL T (b , a) = refl
