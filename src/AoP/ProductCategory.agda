{-# OPTIONS --safe --without-K #-}
module AoP.ProductCategory where

open import AoP.Categories
open import AoP.UniversalObjects using (module Universal)
open import AoP.ArrowCategory using (_×_)
open import Agda.Builtin.Sigma using (fst; snd; _,_)

-- Exercise 2.23. A program in a product category is a pair of arrows,
-- one for each coordinate. A map from the initial pair is forced in both
-- coordinates; reversing the arrows proves the terminal case as well.
module Product {o h e o′ h′ e′} (A : Category o h e) (B : Category o′ h′ e′) where
  private module A = Category A
  private module B = Category B

  prod : Category _ _ _
  Category.Obj prod = A.Obj × B.Obj
  Category.Hom prod x y = A.Hom (fst x) (fst y) × B.Hom (snd x) (snd y)
  Category._≈_ prod f g = (fst f A.≈ fst g) × (snd f B.≈ snd g)
  Category.identity prod = A.identity , B.identity
  Category._∘_ prod g f = (fst g A.∘ fst f) , (snd g B.∘ snd f)
  Category.reflexive prod = A.reflexive , B.reflexive
  Category.symmetric prod (p , q) = A.symmetric p , B.symmetric q
  Category.transitive prod (p , q) (r , s) = A.transitive p r , B.transitive q s
  Category.compose-cong prod (p , q) (r , s) = A.compose-cong p r , B.compose-cong q s
  Category.unitˡ prod (f , g) = A.unitˡ f , B.unitˡ g
  Category.unitʳ prod (f , g) = A.unitʳ f , B.unitʳ g
  Category.assoc prod (f , g) (i , j) (k , l) = A.assoc f i k , B.assoc g j l

  module UA = Universal A
  module UB = Universal B
  module U = Universal prod
  initial : ∀ {a b} → UA.Initial a → UB.Initial b → U.Initial (a , b)
  U.Initial.leave (initial i j) (x , y) = UA.Initial.leave i x , UB.Initial.leave j y
  U.Initial.unique (initial i j) (f , g) = UA.Initial.unique i f , UB.Initial.unique j g

  terminal : ∀ {a b} → UA.Terminal a → UB.Terminal b → U.Terminal (a , b)
  U.Terminal.enter (terminal i j) (x , y) = UA.Terminal.enter i x , UB.Terminal.enter j y
  U.Terminal.unique (terminal i j) (f , g) = UA.Terminal.unique i f , UB.Terminal.unique j g
