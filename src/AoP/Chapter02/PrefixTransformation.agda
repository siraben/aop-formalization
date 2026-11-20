{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.PrefixTransformation where

open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter02.Functors using (Lists; map-comp)
open import AoP.Chapter02.Whiskering using (module Through)
open import AoP.Chapter02.Transformations using (Natural)
open import AoP.Chapter05.ZippedSplits using (inits)

-- §2.3, cons-list version. Every nonempty prefix starts with the same
-- head x. Move relabelling through that common head first, then use the
-- inductive square on the tail. The leading empty prefix stays empty.
private
  backwards : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  backwards refl = refl

prefix-square : ∀ {A B : Set} (f : A → B) xs → map (map f) (inits xs) ≡ inits (map f xs)
prefix-square f [] = refl
prefix-square f (x ∷ xs) = cong ([] ∷_) (begin
  map (map f) (map (x ∷_) ps) ≡⟨ backwards (map-comp (map f) (x ∷_) ps) ⟩
  map (λ ys → f x ∷ map f ys) ps ≡⟨ map-comp (f x ∷_) (map f) ps ⟩
  map (f x ∷_) (map (map f) ps) ≡⟨ cong (map (f x ∷_)) (prefix-square f xs) ⟩
  map (f x ∷_) (inits (map f xs)) ∎)
  where ps = inits xs

prefixes : Natural Lists (Through.compose Lists Lists)
Natural.η prefixes _ = inits
Natural.square prefixes = prefix-square
