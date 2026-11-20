{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.TensorBifunctor where

open import AoP.Common.Prelude
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.Relations using (_←_; _⊆_)
open import AoP.Chapter02.RelationGraphCategory using (Rel)
open import AoP.Chapter02.ProductCategory using (module Product)
open import AoP.Chapter05.RelationalProducts using (_⊗_; mono; id-intro; id-elim)
open import AoP.Chapter05.TensorCompositionByAbsorption using (module Derive)

-- §5.2. The source category has pairs of objects and pairs of
-- relations. Each pair of arrows acts independently on the coordinates
-- of a single product. Composition uses the pairing absorption proof.
tensor : Functor (Product.prod Rel Rel) Rel
Functor.F₀ tensor (A , B) = A × B
Functor.F₁ tensor (R , S) = R ⊗ S
Functor.resp tensor {f = R , S} {g = T , U} ((r , r′) , (s , s′)) = mono R T S U r s , mono T R U S r′ s′
Functor.identity tensor = id-elim , id-intro
Functor.composition tensor (R , S) (U , V) = Derive.backward U V R S , Derive.forward U V R S

-- Enlarging either coordinate relation only adds output pairs.
monotone : ∀ {A B C D} {R R′ : B ← A} {S S′ : D ← C} → R ⊆ R′ → S ⊆ S′ →
  Functor.F₁ tensor (R , S) ⊆ Functor.F₁ tensor (R′ , S′)
monotone = mono _ _ _ _
