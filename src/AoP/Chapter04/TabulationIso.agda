{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.TabulationIso where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_; _˘)
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.TabulationMediator using (module Table)

-- §4.3, consequence of Proposition 4.2. Different row representations
-- of the same relation are interchangeable. In each direction, regard
-- the first table's columns as a span into the second table.
module Compare {A B T U : Set} (R : B ← A) (f : T → B) (g : T → A)
  (h : U → B) (k : U → A)
  (findT : R ⊆ graph f ∘ graph g ˘) (readT : graph f ∘ graph g ˘ ⊆ R)
  (findU : R ⊆ graph h ∘ graph k ˘) (readU : graph h ∘ graph k ˘ ⊆ R)
  (jointT : ∀ x y → f x ≡ f y → g x ≡ g y → x ≡ y)
  (jointU : ∀ x y → h x ≡ h y → k x ≡ k y → x ≡ y) where
  module To = Table.Span R h k findU readU jointU f g
  module From = Table.Span R f g findT readT jointT h k
  to = To.factor readT
  from = From.factor readU
  encode = To.Mediator.row to
  decode = From.Mediator.row from

  -- Each round trip fixes *both* column values. Joint monicity in the
  -- table where we started therefore identifies the row itself.
  recover : ∀ t → decode (encode t) ≡ t
  recover t = jointT _ _ (From.Mediator.target from (encode t) ∙ To.Mediator.target to t)
                         (From.Mediator.source from (encode t) ∙ To.Mediator.source to t)
  restore : ∀ u → encode (decode u) ≡ u
  restore u = jointU _ _ (To.Mediator.target to (decode u) ∙ From.Mediator.target from u)
                         (To.Mediator.source to (decode u) ∙ From.Mediator.source from u)
  unique : ∀ (m : To.Mediator) t → To.Mediator.row m t ≡ encode t
  unique m = To.unique m to
