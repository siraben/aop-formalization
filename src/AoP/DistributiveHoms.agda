{-# OPTIONS --safe --without-K #-}
module AoP.DistributiveHoms where

open import AoP.Prelude

-- Exercise 3.32: calculate maps OUT of the proposed distributed
-- product. An exponential moves the fixed factor across the hom;
-- a coproduct splits the resulting arrow; then uncurry each branch.
-- Hom types here use propositional equality for their inverse laws.
record Bijection (X Y : Set) : Set where
  field to : X → Y
        from : Y → X
        section : ∀ y → to (from y) ≡ y
        retract : ∀ x → from (to x) ≡ x
open Bijection

module Law {Obj : Set} (Hom : Obj → Obj → Set) (_+_ : Obj → Obj → Obj)
           (times exp : Obj → Obj → Obj)
           (curry : ∀ a b t → Bijection (Hom (times a b) t) (Hom a (exp b t)))
           (split : ∀ a b t → Bijection (Hom (a + b) t) (Hom a t × Hom b t))
           (a b c t : Obj) where
  whole = curry (a + b) c t
  cases = split a b (exp c t)
  l = curry a c t
  r = curry b c t

  branches : Bijection (Hom (times (a + b) c) t) (Hom (times a c) t × Hom (times b c) t)
  to branches f with to cases (to whole f)
  ... | u , v = from l u , from r v
  from branches (u , v) = from whole (from cases (to l u , to r v))
  section branches (u , v) rewrite section whole (from cases (to l u , to r v))
                                 | section cases (to l u , to r v) | retract l u | retract r v = refl
  retract branches f with to cases (to whole f) in eq
  ... | u , v rewrite section l u | section r v = cong (from whole) (pair-law eq) ∙ retract whole f
    where pair-law : ∀ {p} → to cases (to whole f) ≡ p → from cases p ≡ to whole f
          pair-law refl = retract cases (to whole f)

  -- Reassemble the two branches as one arrow out of the coproduct
  -- of products. This last step fixes the candidate representing object.
  products = split (times a c) (times b c) t
  distribute : Bijection (Hom (times (a + b) c) t) (Hom (times a c + times b c) t)
  to distribute f = from products (to branches f)
  from distribute g = from branches (to products g)
  section distribute g = begin
    from products (to branches (from branches (to products g)))
      ≡⟨ cong (from products) (section branches (to products g)) ⟩
    from products (to products g) ≡⟨ retract products g ⟩
    g ∎
  retract distribute f = begin
    from branches (to products (from products (to branches f)))
      ≡⟨ cong (from branches) (section products (to branches f)) ⟩
    from branches (to branches f) ≡⟨ retract branches f ⟩
    f ∎
