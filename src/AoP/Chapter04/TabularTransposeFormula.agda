{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.TabularTransposeFormula where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter04.AllegoryMapOrder using () renaming (module Law to Order)
open import AoP.Chapter04.TabularIndirectEquality using (module Law)
open import AoP.Chapter04.SpanDivisionTests using (module In)
open import AoP.Chapter04.SpanColumnShunt using () renaming (module Law to Shunt)

-- §4.6: use equality of the two observed columns to pass between the
-- transpose graph and the intersection of divisions. Transpose
-- uniqueness is needed only for maps with the same membership column.
module Formula {o h e p m} {C : Category o h e} (L : Laws C p)
  (Map : ∀ {A B} → Category.Hom C A B → Set m) where
  open Category C
  open Laws L
  module Derive
    (unit : ∀ {A B} {f : Hom A B} → Map f → identity ⊑ (rev f ∘ f))
    (counit : ∀ {A B} {f : Hom A B} → Map f → (f ∘ rev f) ⊑ identity)
    (compose : ∀ {A B D} {f : Hom A B} {g : Hom B D} → Map g → Map f → Map (g ∘ f))
    (under : ∀ {X Y Z} → Hom Y Z → Hom X Z → Hom X Y)
    (intro : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → (r ∘ x) ⊑ s → x ⊑ under r s)
    (elim : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → x ⊑ under r s → (r ∘ x) ⊑ s) where
    module D = In.Div L under intro elim
    module At {A B P} (mem : Hom P A) (R : Hom B A) (transpose : Hom B P)
      (functional : Map transpose) (cancel : (mem ∘ transpose) ≈ R)
      (unique : ∀ {I} {x y : Hom I P} → Map x → Map y → (mem ∘ x) ≈ (mem ∘ y) → x ≈ y) where
      module T = Law.Test L Map {B} {P}
      tests = meet (under mem R) (rev (under R mem))
      module Row {I} (f : Hom I P) (g : Hom I B) (mf : Map f) (mg : Map g) where
        module Check = D.Test mem R f g (unit mf) (counit mf) (unit mg) (counit mg)
        module G = Shunt.Move L g (unit mg) (counit mg)
        column : (mem ∘ (transpose ∘ g)) ≈ (R ∘ g)
        column = transitive (symmetric (assoc _ _ _)) (compose-cong cancel reflexive)
        forward : (f ∘ rev g) ⊑ transpose → (f ∘ rev g) ⊑ tests
        forward sub = Check.write (transitive (compose-cong reflexive (Order.discrete L f _ (unit mf) (counit (compose functional mg)) (G.across _ _ sub))) column)
        backward : (f ∘ rev g) ⊑ tests → (f ∘ rev g) ⊑ transpose
        backward sub = G.back _ _ (respect (unique mf (compose functional mg) (transitive (Check.read sub) (symmetric column))))
      -- In a tabular allegory both arrows have such factorizations.
      formula : T.Factor transpose → T.Factor tests → transpose ≈ tests
      formula tables columns = T.equality tables columns Row.forward Row.backward

-- For the usual notion of map (entire and simple), all map premises
-- discharge from the allegory laws. Only the division, transpose and
-- tabulation data remain to be supplied by the caller.
module Canonical {o h e p} {C : Category o h e} (L : Laws C p) where
  module M = Maps L
  module Theorem = Formula.Derive L M.Map M.Map.entire M.Map.simple M.compose

  open Category C
  open Laws L
  module Subsets (under : ∀ {X Y Z} → Hom Y Z → Hom X Z → Hom X Y)
    (intro : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → (r ∘ x) ⊑ s → x ⊑ under r s)
    (elim : ∀ {X Y Z} (r : Hom Y Z) (s : Hom X Z) (x : Hom X Y) → x ⊑ under r s → (r ∘ x) ⊑ s)
    {P A} (mem : Hom P A)
    (unique : ∀ {I} {x y : Hom I P} → M.Map x → M.Map y → (mem ∘ x) ≈ (mem ∘ y) → x ≈ y) where
    -- Reflection: identity already transposes membership, because
    -- composing membership with identity leaves its column unchanged.
    module At = Theorem.At under intro elim mem mem identity M.id-map (unitʳ mem) unique
    subset = under mem mem
    antisymmetric : At.T.Factor identity → At.T.Factor At.tests → meet subset (rev subset) ⊑ identity
    antisymmetric i t = respect (symmetric (At.formula i t))
