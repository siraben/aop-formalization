{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryConverseCases where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionaryLastEdge using (module Law)
open import AoP.Chapter09.DictionaryConverseStep using (module Step)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.ShortenPointer using () renaming (module Law to Short)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (suc)

module Cases {A : Set} where
  open Text {A}
  open Step {A}
  open Splice {A} 0 0 using (resume)
  private
    extract : A → List A → List A × A
    extract b [] = [] , b
    extract b (c ∷ cs) with extract c cs
    ... | ys , z = (b ∷ ys) , z
    law : ∀ b xs a → extract b (xs ++ (a ∷ [])) ≡ (b ∷ xs , a)
    law b [] a = refl
    law b (x ∷ xs) a rewrite law x xs a = refl
    view : A → List A → List A × A
    view a [] = [] , a
    view a (b ∷ bs) = extract b bs
    last : ∀ d xs a → view d (xs ++ (a ∷ [])) ≡ (xs , a)
    last d [] a = refl
    last d (b ∷ bs) a = law b bs a
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
    cancel : ∀ xs ys a b → xs ++ (a ∷ []) ≡ ys ++ (b ∷ []) → (xs , a) ≡ (ys , b)
    cancel xs ys a b eq = rev (last a xs a) ∙ cong (view a) eq ∙ last a ys b
    inj : ∀ {x y : List A} → just x ≡ just y → x ≡ y
    inj refl = refl
    copied : ∀ xs i k {ys} → run xs (ptr i k ∷ []) ≡ just ys → copy i (suc k) xs ≡ just ys
    copied xs i k ok with copy i (suc k) xs in eq
    ... | just ys = ok
    ... | nothing with ok
    ...   | ()
    ran : ∀ xs i k {ys} → copy i (suc k) xs ≡ just ys → run xs (ptr i k ∷ []) ≡ just ys
    ran xs i k ok rewrite ok = refl
  Prev : List A → A → List Code → Set
  Prev xs a qs = Σ (List Code) λ ps → (run [] ps ≡ just xs) × Extend a ps qs
  final : ∀ xs a ps op state → run [] ps ≡ just state → run state (op ∷ []) ≡ just (xs ++ (a ∷ [])) → Prev xs a (ps ++ (op ∷ []))
  final xs a ps (sym b) state pre ok with cancel state xs b a (inj ok)
  ... | refl = ps , pre , literal ps
  final xs a ps (ptr i 0) state pre ok with lookup i state in loc
  ... | nothing with ok
  ...   | ()
  final xs a ps (ptr i 0) state pre ok | just b with cancel state xs b a (inj ok)
  ... | refl = ps , pre , begin-ptr ps i state pre loc
  final xs a ps (ptr i (suc k)) state pre ok with copied state i (suc k) ok
  ... | long with Short.shorten i (suc k) state long
  ... | zs , b , short , eq with cancel xs zs a b eq
  ... | refl = _ , (resume [] ps _ pre ∙ ran state i k short) , grow-ptr ps i k state xs pre short long
  complete : ∀ xs a qs → run [] qs ≡ just (xs ++ (a ∷ [])) → Prev xs a qs
  complete [] a [] ()
  complete (_ ∷ _) a [] ()
  complete xs a (o ∷ os) ok with Law.decompose [] o os ok
  ... | Law.edge ps op state eq pre step rewrite eq = final xs a ps op state pre step
