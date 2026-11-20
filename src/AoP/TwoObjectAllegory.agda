{-# OPTIONS --safe --without-K #-}
module AoP.TwoObjectAllegory where

open import AoP.Prelude
open import AoP.ConverseFunctorWitness
open import AoP.ProductAllegory using (Laws)
open import AoP.AllegoryMapComposition using () renaming (module Law to Maps)
open import Agda.Primitive using (lzero)

-- Verify the allegory and the actual tables on the source side of
-- the converse-preserving functor. Bottom is below every arrow;
-- the only other ordered pair is point below itself.
data Le : ∀ {A B} → Arr A B → Arr A B → Set where
  bottom : ∀ {A B} {r : Arr A B} → Le none r
  top : Le point point
same : ∀ {A B} (f : Arr A B) → Le f f
same none = bottom
same point = top
both : ∀ {A B} → Arr A B → Arr A B → Arr A B
both none _ = none
both point f = f
laws : Laws small lzero
Laws._⊑_ laws = Le
Laws.respect laws {f = f} refl = same f
Laws.trans laws bottom q = bottom
Laws.trans laws top q = q
Laws.antisym laws bottom bottom = refl
Laws.antisym laws top top = refl
Laws.meet laws = both
Laws.lower₁ laws none _ = bottom
Laws.lower₁ laws point none = bottom
Laws.lower₁ laws point point = top
Laws.lower₂ laws none _ = bottom
Laws.lower₂ laws point f = same f
Laws.glb laws {f = none} bottom q = bottom
Laws.glb laws {f = point} p q = q
Laws.rev laws = rev
Laws.invol laws none = refl
Laws.invol laws point = refl
Laws.flip laws none none = refl
Laws.flip laws none point = refl
Laws.flip laws point none = refl
Laws.flip laws point point = refl
Laws.rev-mono laws bottom = bottom
Laws.rev-mono laws top = top
Laws.mono laws bottom q = bottom
Laws.mono laws top q = q
Laws.modular laws none f k = bottom
Laws.modular laws point f k = same (both f k)

-- The empty table has no rows. The inhabited table has one row and
-- two identity legs. In each case the common kernel is row identity.
module Tables where
  open Maps laws
  zero-leg : ∀ B → Map (none {nil} {B})
  Map.entire (zero-leg B) = bottom
  Map.simple (zero-leg B) = bottom
  record Table {A B} (r : Arr A B) : Set where
    field rows : Obj
          f : Arr rows B
          g : Arr rows A
          fm : Map f
          gm : Map g
          covers : chain f (rev g) ≡ r
          joint : both (chain (rev f) f) (chain (rev g) g) ≡ id′ rows
  table : ∀ {A B} (r : Arr A B) → Table r
  table none = record { rows = nil; f = none; g = none; fm = zero-leg _; gm = zero-leg _; covers = refl; joint = refl }
  table point = record { rows = one; f = point; g = point; fm = id-map {one}; gm = id-map {one}; covers = refl; joint = refl }
