{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.FoldRetraction where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Initial using (module Theory)

module Derive (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Functor F renaming (F₀ to Layer; F₁ to map)
  open Theory.Initial I
  open Theory.Laws F I using (fusion)
  private
    back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    back refl = refl

  -- Exercise 2.34. If undo recovers every input of m, an algebra on
  -- its output type can undo each child, build a node, and reapply m.
  -- At children produced by m, the undo step cancels pointwise.
  module Section {A : Set} (m : μ → A) (undo : A → μ) (cancel : ∀ x → undo (m x) ≡ x) where
    alg : Layer A → A
    alg t = m (inn (map undo t))

    children : ∀ t → map undo (map m t) ≡ t
    children t = begin
      map undo (map m t) ≡⟨ back (composition undo m t) ⟩
      map (λ x → undo (m x)) t ≡⟨ resp cancel t ⟩
      map (λ x → x) t ≡⟨ identity t ⟩
      t ∎

    as-fold : ∀ x → m x ≡ ⦅ alg ⦆ x
    as-fold = unique alg m (λ t → back (cong (λ s → m (inn s)) (children t)))

  -- Exercise 2.36. To compute an arbitrary f, retain the original
  -- subtree as well as its answer. The second projection undoes this
  -- pairing, so the preceding construction gives its fold algebra.
  module Remember {A : Set} (f : μ → A) where
    save : μ → A × μ
    save x = f x , x
    module S = Section save snd (λ _ → refl)

    projected : ∀ x → f x ≡ fst (⦅ S.alg ⦆ x)
    projected x = cong fst (S.as-fold x)

  -- Exercise 2.35. Slide f across a fold. Precomposing g by map f
  -- on the right supplies precisely the homomorphism equation needed
  -- by fusion: the two sides of that equation agree by computation.
  slide : ∀ {A B : Set} (f : A → B) (g : Layer B → A) x →
          ⦅ (λ t → f (g t)) ⦆ x ≡ f (⦅ (λ t → g (map f t)) ⦆ x)
  slide f g x = back (fusion (λ t → g (map f t)) (λ t → f (g t)) f (λ _ → refl) x)
