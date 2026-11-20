{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ConverseFunctorWitness where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.RelationGraphCategory using (Rel)
open import AoP.Chapter04.Relations using (_←_; _⊆_; _˘)
open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool

-- Decidable relations between the empty set and a singleton. Only the
-- singleton has a nonempty relation, namely its identity. Every empty
-- relation factors through empty rows, and the point through one row.
data Obj : Set where nil one : Obj
data Arr : Obj → Obj → Set where
  none : ∀ {A B} → Arr A B
  point : Arr one one
id′ : (A : Obj) → Arr A A
id′ nil = none
id′ one = point
chain : ∀ {A B C} → Arr B C → Arr A B → Arr A C
chain none _ = none
chain point f = f
small : Category lzero lzero lzero
Category.Obj small = Obj
Category.Hom small = Arr
Category._≈_ small = _≡_
Category.identity small {A} = id′ A
Category._∘_ small = chain
Category.reflexive small = refl
Category.symmetric small refl = refl
Category.transitive small refl refl = refl
Category.compose-cong small refl refl = refl
Category.unitˡ small {B = nil} none = refl
Category.unitˡ small {B = one} f = refl
Category.unitʳ small none = refl
Category.unitʳ small point = refl
Category.assoc small none g f = refl
Category.assoc small point g f = refl

-- Send the empty row object to a singleton and the one-row object to
-- two points. Empty arrows become full rectangles; the singleton
-- identity becomes Boolean equality. Rectangles compose since every
-- target object now has a chosen point.
carrier : Obj → Set
carrier nil = ⊤
carrier one = Bool
pick : (A : Obj) → carrier A
pick nil = tt
pick one = false
lift : ∀ {A B} → Arr A B → carrier B ← carrier A
lift none _ _ = ⊤
lift point = _≡_
image : Functor small Rel
Functor.F₀ image = carrier
Functor.F₁ image = lift
Functor.resp image refl = (λ p → p) , (λ p → p)
Functor.identity image {nil} = (λ _ → refl) , (λ _ → tt)
Functor.identity image {one} = (λ p → p) , (λ p → p)
Functor.composition image {B = B} none none = (λ _ → pick B , tt , tt) , (λ _ → tt)
Functor.composition image none point = (λ _ → _ , tt , refl) , (λ _ → tt)
Functor.composition image point f = Category.unitˡ Rel (lift f) .snd , Category.unitˡ Rel (lift f) .fst
rev : ∀ {A B} → Arr A B → Arr B A
rev none = none
rev point = point
converse : ∀ {A B} (r : Arr A B) → Category._≈_ Rel (lift (rev r)) ((lift r) ˘)
converse none = (λ _ → tt) , (λ _ → tt)
converse point = (λ { refl → refl }) , (λ { refl → refl })

data Empty : Set where
-- Interpret source arrows as actual empty/singleton relations.
base : Obj → Set
base nil = Empty
base one = ⊤
edge : ∀ {A B} → Arr A B → base B ← base A
edge none _ _ = Empty
edge point _ _ = ⊤
source-inclusion : edge (none {one} {one}) ⊆ edge point
source-inclusion ()
-- The source inclusion none ≤ point loses the off-diagonal edge.
lost : (lift (none {one} {one}) ⊆ lift point) → Empty
lost le with le {false} {true} tt
... | ()

-- The mediator from empty rows to a singleton is a map vacuously;
-- its lifted graph relates the single input to *both* Boolean outputs.
mediator = none {nil} {one}
two-outputs : lift mediator false tt × lift mediator true tt
two-outputs = tt , tt
