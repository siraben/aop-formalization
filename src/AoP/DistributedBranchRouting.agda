{-# OPTIONS --safe --without-K #-}
module AoP.DistributedBranchRouting where

open import AoP.Categories
open import AoP.CoproductByDuality using (module Dual)
open import AoP.SpanProduct using (module Over)

-- §3.4. Use distributivity at Bool = 1 + 1 in its universal-property
-- form: (x,true) and (x,false) exhibit X × Bool as a sum of two copies
-- of X. The following construction needs just those particular sums.
module In {o h e} (C : Category o h e) where
  open Category C
  module Product = Over C
  open Dual C
  module Given T t (Bool : Obj) (P : ∀ X → Product.Span X Bool)
    (prod : ∀ X → Product.U.Terminal X Bool (P X)) where
    open Sum T t
    module Pair X = Product.Pair X Bool (prod X)
    payload = λ X → Product.Span.left (P X)
    bit = λ X → Product.Span.right (P X)
    module Branch {A} (p : Hom A Bool) where
      input = Pair.pair A identity p
    module Distributed (select : ∀ X → Hom (Product.Span.apex (P X)) (X ⊕ X))
      -- The inverse comparison injects each tagged copy with its fixed
      -- Boolean. State its two observable coordinates rather than a
      -- choice of representation for the terminal object or its points.
      (unselect : ∀ X → Hom (X ⊕ X) (Product.Span.apex (P X)))
      (inverse : ∀ X → unselect X ∘ select X ≈ identity)
      (payload-law : ∀ X → payload X ∘ unselect X ≈ cases identity identity) where
      tag : ∀ {A} → Hom A Bool → Hom A (A ⊕ A)
      tag {A} p = select A ∘ Branch.input p
      -- Forgetting a selected tag returns its payload. Follow the input
      -- into the product, cancel the two comparisons, then project.
      forget : ∀ {A} (p : Hom A Bool) → cases identity identity ∘ tag p ≈ identity
      forget {A} p = transitive (compose-cong (symmetric (payload-law A)) reflexive)
        (transitive (assoc _ _ _) (transitive (compose-cong reflexive (symmetric (assoc _ _ _)))
        (transitive (compose-cong reflexive (compose-cong (inverse A) reflexive))
        (transitive (compose-cong reflexive (unitˡ _)) (Pair.cancel-left A _ _)))))
      -- When the Boolean coordinate of unselect reads truth from the
      -- tag, truth is a left inverse on tests (exercise 3.25).
      recover : ∀ {A} (truth : Hom (A ⊕ A) Bool) → bit A ∘ unselect A ≈ truth →
                ∀ p → truth ∘ tag p ≈ p
      recover {A} truth reads p = transitive (compose-cong (symmetric reads) reflexive)
        (transitive (assoc _ _ _) (transitive (compose-cong reflexive (symmetric (assoc _ _ _)))
        (transitive (compose-cong reflexive (compose-cong (inverse A) reflexive))
        (transitive (compose-cong reflexive (unitˡ _)) (Pair.cancel-right A _ _)))))

      faithful : ∀ {A} (truth : Hom (A ⊕ A) Bool) → bit A ∘ unselect A ≈ truth →
                 ∀ p q → tag p ≈ tag q → p ≈ q
      faithful truth reads p q eq = transitive (symmetric (recover truth reads p))
        (transitive (compose-cong reflexive eq) (recover truth reads q))

      -- To change the payload before selecting a branch, apply k on
      -- the first product coordinate and leave the Boolean alone.
      carry : ∀ {A B} → Hom A B → Hom (Product.Span.apex (P A)) (Product.Span.apex (P B))
      carry {A} {B} k = Pair.pair B (k ∘ payload A) (bit A)
      module Precompose (natural : ∀ {A B} (k : Hom A B) → select B ∘ carry k ≈ map k k ∘ select A) where
        -- Compare the input pair along each projection. Both routes
        -- pass k as payload and p ∘ k as Boolean.
        align : ∀ {A B} (p : Hom B Bool) (k : Hom A B) → Branch.input p ∘ k ≈ carry k ∘ Branch.input (p ∘ k)
        align {A} {B} p k = transitive (Pair.unique B k (p ∘ k) _
          (transitive (symmetric (assoc _ _ _)) (transitive (compose-cong (Pair.cancel-left B _ _) reflexive) (unitˡ k)))
          (transitive (symmetric (assoc _ _ _)) (compose-cong (Pair.cancel-right B _ _) reflexive)))
          (symmetric (Pair.unique B k (p ∘ k) _
            (transitive (symmetric (assoc _ _ _)) (transitive (compose-cong (Pair.cancel-left B _ _) reflexive)
              (transitive (assoc _ _ _) (transitive (compose-cong reflexive (Pair.cancel-left A _ _)) (unitʳ k)))))
            (transitive (symmetric (assoc _ _ _)) (transitive (compose-cong (Pair.cancel-right B _ _) reflexive) (Pair.cancel-right A _ _)))))
        change : ∀ {A B} (p : Hom B Bool) (k : Hom A B) → tag p ∘ k ≈ map k k ∘ tag (p ∘ k)
        change p k = transitive (assoc _ _ _) (transitive (compose-cong reflexive (align p k))
          (transitive (symmetric (assoc _ _ _)) (transitive (compose-cong (natural k) reflexive) (assoc _ _ _))))
