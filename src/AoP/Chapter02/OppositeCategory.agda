{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.OppositeCategory where

open import AoP.Chapter02.Categories

-- Reverse every arrow but keep its equality. Units exchange sides;
-- associativity in the reversed order uses symmetry of associativity.
op : ∀ {o h e} → Category o h e → Category o h e
Category.Obj (op C) = Category.Obj C
Category.Hom (op C) X Y = Category.Hom C Y X
Category._≈_ (op C) = Category._≈_ C
Category.identity (op C) = Category.identity C
Category._∘_ (op C) g f = Category._∘_ C f g
Category.reflexive (op C) = Category.reflexive C
Category.symmetric (op C) = Category.symmetric C
Category.transitive (op C) = Category.transitive C
Category.compose-cong (op C) p q = Category.compose-cong C q p
Category.unitˡ (op C) = Category.unitʳ C
Category.unitʳ (op C) = Category.unitˡ C
Category.assoc (op C) g f h = Category.symmetric C (Category.assoc C h f g)
