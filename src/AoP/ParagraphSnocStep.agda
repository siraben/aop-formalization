{-# OPTIONS --safe --without-K #-}
module AoP.ParagraphSnocStep where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; weaken; sum-mono; rid)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 8.24. Appending a word acts on the open line. Prefer fewer
-- closed lines, then a narrower open line. If the greedy layout was a
-- break ahead, it can afford to break now; its new singleton line is
-- at least as narrow as either possible rival line.
State = Nat × Nat
infix 4 _≼_
data _≼_ : State → State → Set where
  fewer : ∀ {k j l h} → suc k ≤ j → (k , l) ≼ (j , h)
  narrower : ∀ {k l h} → l ≤ h → (k , l) ≼ (k , h)

module Step (margin : Nat) where
  width : Nat → Nat → Nat
  width w l = w + suc l
  data Next (w : Nat) : State → State → Set where
    glue : ∀ {k l} → width w l ≤ margin → Next w (k , l) (k , width w l)
    line : ∀ {k l} → w ≤ margin → Next w (k , l) (suc k , w)
  private
    decide : ∀ x y → (x ≤ y) ⊎ (x ≤ y → ⊥)
    decide 0 y = inl z≤
    decide (suc x) 0 = inr (λ ())
    decide (suc x) (suc y) with decide x y
    ... | inl p = inl (s≤ p)
    ... | inr n = inr (λ { (s≤ p) → n p })
    pad : ∀ a b → a ≤ a + b
    pad 0 b = z≤
    pad (suc a) b = s≤ (pad a b)
    catch : ∀ {k j l h} → k ≤ j → l ≤ h → (k , l) ≼ (j , h)
    catch {0} {0} le p = narrower p
    catch {0} {suc j} le p = fewer (s≤ z≤)
    catch {suc k} {suc j} (s≤ le) p with catch le p
    ... | fewer lt = fewer (s≤ lt)
    ... | narrower q = narrower q

  choose : Nat → State → State
  choose w (k , l) with decide (width w l) margin
  ... | inl _ = k , width w l
  ... | inr _ = suc k , w
  legal : ∀ w s → w ≤ margin → Next w s (choose w s)
  legal w (k , l) fits with decide (width w l) margin
  ... | inl p = glue p
  ... | inr _ = line fits

  dominates : ∀ w {s t u} → s ≼ t → Next w t u → choose w s ≼ u
  dominates w (fewer {l = l} lt) (glue {l = h} f) with decide (width w l) margin
  ... | inl _ = fewer lt
  ... | inr _ = catch lt (pad w (suc h))
  dominates w (fewer {l = l} lt) (line f) with decide (width w l) margin
  ... | inl _ = fewer (weaken lt)
  ... | inr _ = fewer (s≤ lt)
  dominates w (narrower {l = l} p) (glue f) with decide (width w l) margin
  ... | inl _ = narrower (sum-mono (rid w) (s≤ p))
  ... | inr n with n (chain (sum-mono (rid w) (s≤ p)) f)
  ...   | ()
  dominates w (narrower {l = l} p) (line f) with decide (width w l) margin
  ... | inl _ = fewer (rid _)
  ... | inr _ = narrower (rid w)
