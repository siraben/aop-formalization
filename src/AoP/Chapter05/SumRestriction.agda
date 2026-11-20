{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SumRestriction where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter05.RelationalSums using (_⊕_; left; right)
open import AoP.Chapter05.CopairCancellation using (copair)

-- Exercise 5.14. Restrict a tag-preserving sum step to pairs that
-- can reach a common observation. The sum fixes both tags, so on the
-- left branch the common observation comes from u and P, and on the
-- right it comes from v and Q. Mixed cases cannot survive the meet.
module Law {A B C D E : Set} (R : C ← A) (S : D ← B)
           (u : E ← C) (v : E ← D) (P : E ← A) (Q : E ← B) where
  whole = (R ⊕ S) ⊓ (copair u v ˘ ∘ copair P Q)
  parts = (R ⊓ (u ˘ ∘ P)) ⊕ (S ⊓ (v ˘ ∘ Q))

  distribute : whole ⊆ parts
  distribute (left r , e , ue , pe) = left (r , e , ue , pe)
  distribute (right s , e , ve , qe) = right (s , e , ve , qe)

  collect : parts ⊆ whole
  collect (left (r , e , ue , pe)) = left r , e , ue , pe
  collect (right (s , e , ve , qe)) = right s , e , ve , qe
