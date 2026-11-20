{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.FiniteFrontierClosure where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Common.NatOrder using (_≤_; rid; z≤; s≤)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter06.ClosureFrontierInvariant using (module Search)
open import AoP.Chapter06.FiniteFrontierBudget using (Dec; size; module Scan)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §6.7. A finite cover of the reachable vertices suffices even when
-- A is infinite. The cover may contain duplicates and unreachable entries.
module Covered {A : Set} (verts : List A)
  (R : A ← A) (edge : ∀ y x → Dec (R y x)) (seed : A → Set) (initial : ∀ x → Dec (seed x))
  (all : ∀ x → Search.Reach R seed x → x ∈ verts) where
  open Search R seed
  private
    both : ∀ {P Q} → Dec P → Dec Q → Dec (P × Q)
    both (inl p) (inl q) = inl (p , q)
    both (inr n) _ = inr (λ z → n (fst z))
    both _ (inr n) = inr (λ z → n (snd z))
    either : ∀ {P Q} → Dec P → Dec Q → Dec (P ⊎ Q)
    either (inl p) _ = inl (inl p)
    either _ (inl q) = inl (inr q)
    either (inr p) (inr q) = inr λ { (inl x) → p x ; (inr y) → q y }
    neg : ∀ {P} → Dec P → Dec (P → ⊥)
    neg (inl p) = inr (λ n → n p)
    neg (inr n) = inl n
    exists : ∀ P → (∀ x → P x → Reach x) → (∀ x → Dec (P x)) → Dec (Σ A P)
    exists P reachable dec with Scan.scan P dec verts
    ... | inl h = inl (Scan.Hit.point h , Scan.Hit.active h)
    ... | inr n = inr (λ { (x , p) → n (all x (reachable x p)) p })

  -- Return a membership decision for every vertex. On an empty frontier,
  -- convert the current finished-set decision by the invariant's stop rule.
  Answer = ∀ x → Dec (Reach x)
  loop : ∀ fuel tokens → size tokens ≤ fuel → ∀ {P Q} → (s : State P Q) →
    (∀ x → Dec (P x)) → (∀ x → Dec (Q x)) → (∀ x → Q x → P x → ⊥) →
    (∀ x → Reach x → (P x → ⊥) → x ∈ tokens) → Answer
  loop fuel tokens budget {P} {Q} s dp dq disjoint cover with Scan.scan Q dq tokens
  ... | inr none = answer
    where
      module End = Round.Stop s (λ x q → none (cover x (State.sound s x (inr q)) (disjoint x q)) q)
      answer : Answer
      answer x with dp x
      ... | inl p = inl (End.correct x p)
      ... | inr absent = inr (λ path → absent (End.complete x path))
  loop zero tokens budget {Q = Q} s dp dq disjoint cover | inl h with size tokens | Scan.Hit.cost h | budget
  ... | .(suc _) | refl | ()
  loop (suc k) tokens budget {P} {Q} s dp dq disjoint cover | inl h =
    loop k rest smaller (Round.step s seen) seen fresh (λ _ v → snd v)
      (λ x path n → keep (λ q → n (inr q)) (cover x path (λ p → n (inl p))))
    where
      open Scan.Hit h
      smaller : size rest ≤ k
      smaller = shrink cost budget
        where shrink : ∀ {m n k} → m ≡ suc n → m ≤ suc k → n ≤ k
              shrink refl (s≤ b) = b
      seen = λ x → either (dp x) (dq x)
      fresh : ∀ y → Dec (Round.Fresh s y)
      fresh y = both (exists _ (λ x pair → State.sound s x (inr (fst pair))) (λ x → both (dq x) (edge y x))) (neg (seen y))

  solve : Answer
  solve = loop (size verts) verts (rid _) start (λ _ → inr (λ z → z)) initial (λ _ _ z → z) (λ x path _ → all x path)

  -- Turn the shared membership decision into an enumeration. Filtering
  -- preserves the order and multiplicity of the supplied cover.
  private
    open import AoP.Chapter07.FilterGreedy using (module Law)
    open import AoP.Chapter08.SortedFilter using (module Restrict)
    module Select = Law Reach solve
    module Members = Restrict (_≡_) Reach solve
  vertices = Select.filter verts
  listed : ∀ x → x ∈ vertices → Reach x
  listed x m = snd (Members.sound verts x m)
  found : ∀ x → Reach x → x ∈ vertices
  found x p = Members.complete verts x (all x p) p

-- A finite universe provides a cover without any graph-specific proof.
module Graph {A : Set} (verts : List A) (all : ∀ x → x ∈ verts)
  (R : A ← A) (edge : ∀ y x → Dec (R y x)) (seed : A → Set) (initial : ∀ x → Dec (seed x)) where
  open Covered verts R edge seed initial (λ x _ → all x) public
