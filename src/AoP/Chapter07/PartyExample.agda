{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.PartyExample where

-- Run the company-party algorithm on a three-person hierarchy. Ada,
-- rated 8, supervises Bo and Cy, rated 5 each. No employee can attend
-- with their direct supervisor. These equations test both versions of
-- the invitation problem by computing their actual answers.
open import AoP.Common.Prelude
open import AoP.Chapter07.Party using (module Planning)
open import AoP.Chapter07.PartyCachedPlan using (module Law)
open import AoP.Chapter01.Trees using (fork; grow; null)
open import Agda.Builtin.Nat using (Nat; zero; _+_)
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono; compare)

data Person : Set where Ada Bo Cy : Person
rating : Person → Nat
rating Ada = 8
rating Bo = 5
rating Cy = 5

open Planning rating zero _+_ _≤_ rid chain sum-mono compare
reports = grow (fork Bo null) (grow (fork Cy null) null)

-- With no compulsory guests, the two reports together score 10.
ordinary : invitations (fork Ada reports) ≡ Bo ∷ Cy ∷ []
ordinary = refl

-- Requiring Ada costs two points; neither direct report may attend.
mandatory : presidential-invitations Ada reports ≡ Ada ∷ []
mandatory = refl

module Cached = Law rating zero _+_ _≤_ rid chain sum-mono compare
cached-ordinary : Cached.guests (fork Ada reports) ≡ Bo ∷ Cy ∷ []
cached-ordinary = refl
cached-mandatory : Cached.with-president Ada reports ≡ Ada ∷ []
cached-mandatory = refl
cached-president-score : Cached.Entry.cached (Cached.mandatory Ada reports) ≡ 8
cached-president-score = refl
