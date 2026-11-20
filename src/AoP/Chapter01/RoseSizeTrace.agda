{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.RoseSizeTrace where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Rose; Forest; fork; null; grow; rose-size; module RoseFold)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- §1.4: how many labelled nodes occur in a tree with arbitrarily
-- many children? Each node contributes one; a forest adds its tree
-- sizes. A singleton child forest and an empty one have different roles.
data Label : Set where root branch leaf bud : Label
module Count = RoseFold {Label} (λ _ n → suc n) 0 _+_
child : Rose Label
child = fork branch (grow (fork bud null) null)
children : Forest Label
children = grow child (grow (fork leaf null) null)

trace : rose-size (fork root children) ≡ 4
trace = begin
  rose-size (fork root children) ≡⟨⟩
  suc (Count.forest children) ≡⟨⟩
  suc (Count.tree child + (Count.tree (fork leaf null) + 0)) ≡⟨⟩
  suc (suc (Count.tree (fork bud null) + 0) + (1 + 0)) ≡⟨⟩
  suc (2 + 1) ≡⟨⟩
  4 ∎
