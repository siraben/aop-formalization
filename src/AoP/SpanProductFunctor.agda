{-# OPTIONS --safe --without-K #-}
module AoP.SpanProductFunctor where

open import AoP.Categories
open import AoP.SpanProduct using (module Over)
open import AoP.ProductCategory using (module Product)
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.ProductProjectionFunctors using (module Projections)
open import Agda.Builtin.Sigma using (fst; snd; _,_)

-- §2.5. Choose a terminal span for each pair of endpoints. To transport
-- its apex along (f,g), observe the old apex through f and g, then pair
-- those observations at the new apex. Uniqueness turns two projection
-- calculations into an equality between the whole arrows.
module Build {o h e} (C : Category o h e) where
  open Category C
  module S = Over C
  module P = Product C C
  module Chosen (T : ∀ A B → S.Span A B)
                (term : ∀ A B → S.U.Terminal A B (T A B)) where
    module Pair {A B} = S.Pair A B (term A B)
    apex = λ A B → S.Span.apex (T A B)
    left = λ A B → S.Span.left (T A B)
    right = λ A B → S.Span.right (T A B)
    cross : ∀ {A B D E} → Hom A D → Hom B E → Hom (apex A B) (apex D E)
    cross {A} {B} f g = Pair.pair (f ∘ left A B) (g ∘ right A B)

    -- (2.8) First fuse precomposition through a pairing by testing the
    -- two projections. Then the two inner projections cancel against
    -- the supplied pair: no inspectable representation of pairs is used.
    fusion : ∀ {A B X Y} (p : Hom X A) (q : Hom X B) (m : Hom Y X) →
      Pair.pair p q ∘ m ≈ Pair.pair (p ∘ m) (q ∘ m)
    fusion p q m = Pair.unique _ _ _
      (transitive (symmetric (assoc _ _ _)) (compose-cong (Pair.cancel-left p q) reflexive))
      (transitive (symmetric (assoc _ _ _)) (compose-cong (Pair.cancel-right p q) reflexive))

    absorption : ∀ {A B D E X} (f : Hom A D) (g : Hom B E) (p : Hom X A) (q : Hom X B) →
      cross f g ∘ Pair.pair p q ≈ Pair.pair (f ∘ p) (g ∘ q)
    absorption {A} {B} f g p q = transitive (fusion (f ∘ left A B) (g ∘ right A B) (Pair.pair p q))
      (Pair.unique _ _ _
        (transitive (Pair.cancel-left _ _) (transitive (assoc _ _ _) (compose-cong reflexive (Pair.cancel-left p q))))
        (transitive (Pair.cancel-right _ _) (transitive (assoc _ _ _) (compose-cong reflexive (Pair.cancel-right p q)))))

    -- The same calculation applies to either projection: associate,
    -- cancel the outer pairing, reassociate, cancel the inner pairing.
    path : ∀ {I J K X Y Z} (p : Hom K Z) (s : Hom J K) (t : Hom I J)
      (g : Hom Y Z) (q : Hom J Y) (f : Hom X Y) (r : Hom I X) →
      p ∘ s ≈ g ∘ q → q ∘ t ≈ f ∘ r → p ∘ (s ∘ t) ≈ (g ∘ f) ∘ r
    path p s t g q f r outer inner = transitive (symmetric (assoc p s t))
      (transitive (compose-cong outer reflexive) (transitive (assoc g q t)
      (transitive (compose-cong reflexive inner) (symmetric (assoc g f r)))))

    product : Functor P.prod C
    Functor.F₀ product (A , B) = apex A B
    Functor.F₁ product (f , g) = cross f g
    Functor.resp product (u , v) = Pair.unique _ _ _
      (transitive (Pair.cancel-left _ _) (compose-cong u reflexive))
      (transitive (Pair.cancel-right _ _) (compose-cong v reflexive))
    Functor.identity product = symmetric (Pair.unique _ _ identity
      (transitive (unitʳ _) (symmetric (unitˡ _))) (transitive (unitʳ _) (symmetric (unitˡ _))))
    Functor.composition product (g , k) (f , h) = symmetric (Pair.unique _ _ _
      (path _ _ _ g _ f _ (Pair.cancel-left _ _) (Pair.cancel-left _ _))
      (path _ _ _ k _ h _ (Pair.cancel-right _ _) (Pair.cancel-right _ _)))

    -- The component of each transformation is a leg of the chosen
    -- span. Naturality asks whether observing before or after transport
    -- changes the answer: the cancellation equation is exactly the square.
    left-projection : Natural product (Projections.left C C)
    Natural.η left-projection (A , B) = left A B
    Natural.square left-projection (f , g) = symmetric (Pair.cancel-left _ _)
    right-projection : Natural product (Projections.right C C)
    Natural.η right-projection (A , B) = right A B
    Natural.square right-projection (f , g) = symmetric (Pair.cancel-right _ _)

    -- The alternative derivation in the text substitutes the two legs
    -- of cross f h for the inputs of absorption, then reassociates.
    via-absorption : ∀ {A B D E I J} (g : Hom D I) (k : Hom E J) (f : Hom A D) (h : Hom B E) →
      cross g k ∘ cross f h ≈ cross (g ∘ f) (k ∘ h)
    via-absorption {A} {B} g k f h = transitive (absorption g k (f ∘ left A B) (h ∘ right A B))
      (Pair.unique _ _ _ (transitive (Pair.cancel-left _ _) (symmetric (assoc _ _ _)))
                         (transitive (Pair.cancel-right _ _) (symmetric (assoc _ _ _))))
