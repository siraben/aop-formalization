{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.AutomatonFibreFold where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (_≐_)
open import AoP.Chapter04.Relations using (Fold)
open import AoP.Chapter05.ListFoldByMembership using (module Calculate)
open import Agda.Builtin.Bool

-- A small illustration of §5.5. Read the list from its tail. On
-- 'guess' an idle machine may stay idle or arm itself; 'finish'
-- accepts only from armed. No transition leaves the accepting state.
data Letter : Set where guess finish : Letter
data State : Set where idle armed accepted : State
data Step : State → Letter × State → Set where
  stay : Step idle (guess , idle)
  arm : Step armed (guess , idle)
  accept : Step accepted (finish , armed)
Base : State → Set
Base s = s ≡ idle
module Runs = Calculate Base Step

-- An executable deterministic state encodes the three possible
-- answers with membership bits, in idle/armed/accepted order.
record Bits : Set where
  constructor bits
  field i a ok : Bool
open Bits
holds : Bool → Set
holds b = b ≡ true
member : Bits → State → Set
member z idle = holds (i z)
member z armed = holds (a z)
member z accepted = holds (ok z)
next : Letter → Bits → Bits
next guess z = bits (i z) (i z) false
next finish z = bits false false (a z)
run : List Letter → Bits
run [] = bits true false false
run (l ∷ ls) = next l (run ls)

base : member (run []) ≐ Base
fst base idle p = refl
fst base armed ()
fst base accepted ()
snd base .idle refl = refl
layer : ∀ l z → member (next l z) ≐ Runs.extend l (member z)
fst (layer guess z) idle p = idle , p , stay
fst (layer guess z) armed p = idle , p , arm
fst (layer guess z) accepted ()
fst (layer finish z) idle ()
fst (layer finish z) armed ()
fst (layer finish z) accepted p = armed , p , accept
snd (layer guess z) _ (_ , p , stay) = p
snd (layer guess z) _ (_ , p , arm) = p
snd (layer finish z) _ (_ , p , accept) = p
module Certificate = Runs.Rival (λ s ls → member (run ls) s) base (λ l ls → layer l (run ls))
correct : ∀ ls → member (run ls) ≐ (λ s → Fold Base Step s ls)
fst (correct ls) s p = Runs.sound (fst (Certificate.only ls) s p)
snd (correct ls) s p = snd (Certificate.only ls) s (Runs.complete p)

branch : run (guess ∷ []) ≡ bits true true false
branch = refl
finish-trace : run (finish ∷ guess ∷ []) ≡ bits false false true
finish-trace = refl
