{-# OPTIONS --safe --without-K #-}
module AoP.TourArmNormal where

open import AoP.Prelude
open import AoP.Subsequences using (_∈_; here; there; split; preimage)
open import AoP.OrderedMeet using (module Order)
open import AoP.Naturality using (_++_)
open import AoP.TourKeyLayer using (module Keys)
open import AoP.TourKeyNormal using (module Normal)
open import AoP.TourThinProjection using (module Law)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)

private
  Diff : ∀ {A : Set} → A → A → Set
  Diff x y = x ≡ y → ⊥
  Unique : ∀ {A : Set} → List A → Set
  Unique = Order.Ordered Diff
  join : ∀ {A : Set} (xs ys : List A) → Unique xs → Unique ys →
         (∀ {x y} → x ∈ xs → y ∈ ys → Diff x y) → Unique (xs ++ ys)
  join [] ys ux uy apart = uy
  join (x ∷ xs) ys (Order.cons head rest) uy apart = Order.cons bound (join xs ys rest uy (λ m → apart (there m)))
    where bound : ∀ {z} → z ∈ (xs ++ ys) → Diff x z
          bound m with split xs ys m
          ... | inl l = head l
          ... | inr r = apart here r

module Law′ (City : Set) where
  open Keys City
  leftU : ∀ b xs → Unique xs → Unique (L b xs)
  leftU b [] _ = Order.nil
  leftU b (x ∷ xs) (Order.cons h u) = Order.cons bound (leftU b xs u)
    where bound : ∀ {z} → z ∈ L b xs → Diff (x , b) z
          bound m with preimage (λ a → a , b) xs m
          ... | a , p , refl = λ eq → h p (cong fst eq)
  rightU : ∀ b xs → Unique xs → Unique (R b xs)
  rightU b [] _ = Order.nil
  rightU b (x ∷ xs) (Order.cons h u) = Order.cons bound (rightU b xs u)
    where bound : ∀ {z} → z ∈ R b xs → Diff (b , x) z
          bound m with preimage (λ a → b , a) xs m
          ... | a , p , refl = λ eq → h p (cong snd eq)
  module At (eq : ∀ (p q : Key) → (p ≡ q) ⊎ Diff p q) where
    open Normal eq
    open Law {Tour = Key} (λ k → k) (λ _ → 0) eq using (compact)
    apart : ∀ {xs} → Unique xs → Apart xs
    apart Order.nil = empty
    apart (Order.cons {xs = []} h u) = single _
    apart (Order.cons {xs = y ∷ ys} h u) = cons (h here) (apart u)
    normal : ∀ b xs ys → Unique xs → Unique ys → (b ∈ xs → ⊥) →
             compact (L b xs ++ R b ys) ≡ L b xs ++ R b ys
    normal b xs ys ux uy fresh = fixed (apart (join (L b xs) (R b ys) (leftU b xs ux) (rightU b ys uy) separate))
      where separate : ∀ {p q} → p ∈ L b xs → q ∈ R b ys → Diff p q
            separate l r with preimage (λ a → a , b) xs l | preimage (λ a → b , a) ys r
            ... | x , m , refl | y , n , refl = λ { refl → fresh m }
