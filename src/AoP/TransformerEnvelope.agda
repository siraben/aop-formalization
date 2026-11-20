{-# OPTIONS --safe --without-K #-}
module AoP.TransformerEnvelope where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Power using (ℙ)
open import AoP.LiberalPrecondition using (wlp)

-- Exercise 4.52, last part. At input a collect all the postconditions
-- for which p accepts a. A possible output must pass *every* one.
-- No monotonicity assumption on p is needed. Quantifying over all
-- small predicates gives a large edge type, even for small A and B.
module Build {A B : Set} (p : ℙ B → ℙ A) where
  S : B → A → Set₁
  S b a = (post : ℙ B) → p post a → post b

  -- wlp of this large relation, tested on the original small posts.
  envelope : ℙ B → A → Set₁
  envelope post a = ∀ {b} → S b a → post b

  extensive : ∀ post a → p post a → envelope post a
  extensive post a accepted edge = edge post accepted

  module Test (R : B ← A) where
    Below = ∀ post a → p post a → wlp R post a
    ClosedBelow = ∀ post a → envelope post a → wlp R post a

    -- Each R edge must satisfy every obligation imposed by p. Thus
    -- each is an S edge and any universal guarantee for S applies to R.
    include : Below → ∀ {a b} → R b a → S b a
    include le {a} r post accepted = le post a accepted r
    least : Below → ClosedBelow
    least le post a guaranteed r = guaranteed (include le r)
    reflect : ClosedBelow → Below
    reflect le post a accepted = le post a (extensive post a accepted)

  -- A local small presentation suffices to stay in the earlier Rel
  -- interface. Only logical equivalence of edge types is necessary.
  module Small (T : B ← A) (encode : ∀ {a b} → S b a → T b a)
    (decode : ∀ {a b} → T b a → S b a) (R : B ← A) where
    Bound = ∀ post a → wlp T post a → wlp R post a
    least : Test.Below R → Bound
    least le post a all r = all (encode (Test.include R le r))
    reflect : Bound → Test.Below R
    reflect le post a accepted = le post a (λ t → decode t post accepted)
