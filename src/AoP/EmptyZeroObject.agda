{-# OPTIONS --safe --without-K #-}
module AoP.EmptyZeroObject where

open import AoP.Complement using (⊥)
open import AoP.Prelude
open import AoP.Categories using (Category)
open import AoP.RelationGraphCategory using (Rel)
open import AoP.PartialGraphCategory using (Par; partial)
open import AoP.UniversalObjects using (module Universal)

-- §2.4. A relation into the empty type cannot have an edge: such an
-- edge would have an output there. Dually, a relation out of the empty
-- type would need an input there. Thus the empty graph is forced in
-- both directions. It also satisfies the partial-function restriction.
module R = Universal Rel
module P = Universal Par
terminal : R.Terminal ⊥
R.Terminal.enter terminal A b a = ⊥
R.Terminal.unique terminal f = (λ { {b = ()} }) , (λ ())
initial : R.Initial ⊥
R.Initial.leave initial A b a = ⊥
R.Initial.unique initial f = (λ { {a = ()} }) , (λ ())

partial-terminal : P.Terminal ⊥
P.Terminal.enter partial-terminal A = partial (R.Terminal.enter terminal A) (λ ())
P.Terminal.unique partial-terminal f = R.Terminal.unique terminal _
partial-initial : P.Initial ⊥
P.Initial.leave partial-initial A = partial (R.Initial.leave initial A) (λ ())
P.Initial.unique partial-initial f = R.Initial.unique initial _
