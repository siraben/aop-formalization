{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ConcreteAllegory where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.RelationGraphCategory using (Rel)
open import AoP.Chapter04.ProductAllegory using (Laws)
open import Agda.Primitive using (lzero)

-- Interpret the abstract calculation rules using actual relation
-- witnesses. Reversing a composed path exchanges its two edges and
-- leaves its intermediate vertex untouched.
laws : Laws Rel lzero
Laws._⊑_ laws = _⊆_
Laws.respect laws = fst
Laws.trans laws sub sub′ edge = sub′ (sub edge)
Laws.antisym laws sub sub′ = sub , sub′
Laws.meet laws = _⊓_
Laws.lower₁ laws _ _ = fst
Laws.lower₂ laws _ _ = snd
Laws.glb laws left right edge = left edge , right edge
Laws.rev laws = _˘
Laws.invol laws _ = (λ x → x) , (λ x → x)
Laws.flip laws _ _ = (λ { (b , r , s) → b , s , r }) , (λ { (b , s , r) → b , r , s })
Laws.rev-mono laws sub = sub
Laws.mono laws left right (b , l , r) = b , left l , right r
Laws.modular laws = modular
