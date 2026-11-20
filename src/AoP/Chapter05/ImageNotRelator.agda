{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ImageNotRelator where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (ℙ; ℰ; _≐_)
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 5.15. Existential image is monotone in its input subset.
-- For it to be a relator, its *graph* would also have to be monotone
-- in the input relation. Enlarge the empty relation on a singleton by
-- adding its sole possible edge. The empty output set disappears from
-- the graph at the full input set, even though we only added an edge.
none every : ⊤ ← ⊤
none _ _ = ⊥
every _ _ = ⊤

sub : none ⊆ every
sub ()

full empty : ℙ ⊤
full _ = ⊤
empty _ = ⊥

before : ℰ none full ≐ empty
before = (λ { _ (_ , p , _) → p }) , (λ { _ () })
after-impossible : ℰ every full ≐ empty → ⊥
after-impossible eq = fst eq tt (tt , tt , tt)

fails : ((ℰ none full ≐ empty) → (ℰ every full ≐ empty)) → ⊥
fails monotone = after-impossible (monotone before)
