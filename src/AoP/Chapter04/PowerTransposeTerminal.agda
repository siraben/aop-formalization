{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.PowerTransposeTerminal where

open import Agda.Primitive using (_⊔_)
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.UniversalObjects using (module Universal)

-- §4.6. J embeds functions into relations in the intended application.
-- Fix the output A. Objects are relations into A; a morphism changes
-- the input by a function whose graph preserves the relation. Stating
-- the construction for a functor J avoids assuming a small powerset.
module Slice {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) (A : Category.Obj D) where
  private module C = Category C
  private module D = Category D
  private module J = Functor J
  record Object : Set (o ⊔ h′) where
    constructor obj
    field input : C.Obj
          relation : D.Hom (J.F₀ input) A
  open Object
  record Change (X Y : Object) : Set (h ⊔ e′) where
    constructor via
    field run : C.Hom (input X) (input Y)
          triangle : (relation Y D.∘ J.F₁ run) D.≈ relation X
  open Change
  slice : Category _ _ _
  Category.Obj slice = Object
  Category.Hom slice = Change
  Category._≈_ slice f g = run f C.≈ run g
  Category.identity slice = via C.identity (D.transitive (D.compose-cong D.reflexive J.identity) (D.unitʳ _))
  Category._∘_ slice g f = via (run g C.∘ run f) (D.transitive (D.compose-cong D.reflexive (J.composition _ _))
    (D.transitive (D.symmetric (D.assoc _ _ _)) (D.transitive (D.compose-cong (triangle g) D.reflexive) (triangle f))))
  Category.reflexive slice = C.reflexive
  Category.symmetric slice = C.symmetric
  Category.transitive slice = C.transitive
  Category.compose-cong slice = C.compose-cong
  Category.unitˡ slice f = C.unitˡ _
  Category.unitʳ slice f = C.unitʳ _
  Category.assoc slice g f k = C.assoc _ _ _

  module U = Universal slice
  module Power (P : C.Obj) (member : D.Hom (J.F₀ P) A) where
    -- Reading membership after the transpose recovers the original
    -- relation. Every other function with that property must agree.
    record Laws : Set (o ⊔ h′ ⊔ h ⊔ e′ ⊔ e) where
      field transpose : ∀ X → C.Hom (input X) P
            cancel : ∀ X → (member D.∘ J.F₁ (transpose X)) D.≈ relation X
            only : ∀ X f → (member D.∘ J.F₁ f) D.≈ relation X → f C.≈ transpose X
    from-terminal : U.Terminal (obj P member) → Laws
    Laws.transpose (from-terminal t) X = run (U.Terminal.enter t X)
    Laws.cancel (from-terminal t) X = triangle (U.Terminal.enter t X)
    Laws.only (from-terminal t) X f eq = U.Terminal.unique t (via f eq)
    to-terminal : Laws → U.Terminal (obj P member)
    U.Terminal.enter (to-terminal l) X = via (Laws.transpose l X) (Laws.cancel l X)
    U.Terminal.unique (to-terminal l) f = Laws.only l _ (run f) (triangle f)

    module Derived (laws : Laws) where
      open Laws laws
      -- Identity already solves the membership triangle. This
      -- specializes the uniqueness clause to membership itself.
      reflection : C.identity C.≈ transpose (obj P member)
      reflection = only _ _ (D.transitive (D.compose-cong D.reflexive J.identity) (D.unitʳ _))

      -- Precompose R by the graph of a function f. The graph gives a
      -- slice morphism back to R; paste it with the unique terminal map.
      -- Its uniqueness says that transposing after precomposition is
      -- the same as applying the original fibre function after f.
      fusion : ∀ X {B} (f : C.Hom B (input X)) →
        (transpose X C.∘ f) C.≈ transpose (obj B (relation X D.∘ J.F₁ f))
      fusion X f = U.Terminal.fusion (to-terminal laws) (via f D.reflexive)
