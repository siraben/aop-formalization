{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.CategoricalDistributedCase where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.SpanProductFunctor using (module Build)
open import AoP.Chapter02.CoproductByDuality using (module Dual)
open import AoP.Chapter02.Functors using (Functor)
open import Agda.Builtin.Sigma using (_,_)

-- Exercise 3.28. The canonical comparison includes either tagged
-- product into a product with a tagged second coordinate. Applying
-- a case analysis after that comparison selects the matching handler.
module In {o h e} (C : Category o h e) where
  open Category C
  module Given P pt S st where
    open Build.Chosen C P pt using (apex; cross; product; via-absorption)
    open Dual.Sum C S st using (_⊕_; cases; inl; inr; cancel-left; cancel-right; fusion; module D)
    module At (A B E : Obj) where
      Src = apex A B ⊕ apex A E
      Dest = apex A (B ⊕ E)
      join : Hom Src Dest
      join = cases (cross identity inl) (cross identity inr)
      module Handlers {X Y} (f : Hom A X) (g : Hom B Y) (k : Hom E Y) where
        apply = cross f (cases g k)
        branches = cases (cross f g) (cross f k)
        left : apply ∘ cross identity inl ≈ cross f g
        left = transitive (via-absorption f _ identity inl) (Functor.resp product (unitʳ f , cancel-left g k))
        right : apply ∘ cross identity inr ≈ cross f k
        right = transitive (via-absorption f _ identity inr) (Functor.resp product (unitʳ f , cancel-right g k))
        -- This direction holds even when distribution has no inverse.
        on-tags : apply ∘ join ≈ branches
        on-tags = transitive (fusion apply _ _) (D.Pair.unique _ _ _
          (transitive (cancel-left _ _) left) (transitive (cancel-right _ _) right))
        -- To recover the requested orientation it suffices to have
        -- join after distribute equal identity on the original input.
        distribute-case : (distribute : Hom Dest Src) → join ∘ distribute ≈ identity → apply ≈ branches ∘ distribute
        distribute-case distribute undo = transitive (symmetric (unitʳ apply))
          (transitive (compose-cong reflexive (symmetric undo))
          (transitive (symmetric (assoc _ _ _)) (compose-cong on-tags reflexive)))
