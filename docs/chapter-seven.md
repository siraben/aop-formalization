# Chapter 7: optimisation problems

## §7.1 Minimum and maximum

[TwoMinima](../src/AoP/TwoMinima.agda) proves exercise 7.8 for concrete reflexive relations `R` and `S`. If `R a b` and `S b a`, the set `{a,b}` has `a` as an `R`-minimum and `b` as an `S`-minimum. Conversely, any set witnessing those two minima gives the two comparisons. The reverse implication uses only membership and the lower-bound property; reflexivity enters when constructing the witness.

[MinimumComparison](../src/AoP/MinimumComparison.agda) derives exercises 7.9–7.10. Taking the second relation in 7.8 to be universal recovers `R a b` from a set containing `b` with `a` as an `R`-minimum. Testing inclusion of minima on that witness recovers inclusion of the underlying relations. Only `R` needs to be reflexive for this direction.

[UniqueMinimum](../src/AoP/UniqueMinimum.agda) checks exercise 7.11 for reflexive relations. Antisymmetry gives at most one minimum on each set. Conversely, the shared two-element witness from 7.8 turns uniqueness into antisymmetry. The reflexivity hypothesis matters for this converse: a two-cycle without self-loops has no minima and fails antisymmetry.

[LowerMinimum](../src/AoP/LowerMinimum.agda) proves exercises 7.5 and 7.12 for preorders. Transitivity makes every predecessor of a lower bound another lower bound; reflexivity supplies the converse witness. A member of a set is a minimum exactly when it precedes some minimum of that set.

[PrincipalMaximum](../src/AoP/PrincipalMaximum.agda) proves exercise 7.14. The maxima of the predecessors of `a` are exactly the elements `b` satisfying both `R b a` and `R a b`. This allows distinct maxima in a preorder.

[MinimumMeet](../src/AoP/MinimumMeet.agda) checks exercises 7.6 and 7.13. A minimum for the intersection of two relations is precisely a member minimizing both. Restricting a preorder to pairs with equal images under a function also preserves reflexivity and transitivity.

[ProductMinimum](../src/AoP/ProductMinimum.agda) checks exercise 7.15 for independent choices from two result sets at a common input. Pairing their minima gives a minimum for the componentwise comparison; the two components may have different types and comparison relations.

[TieMinimum](../src/AoP/TieMinimum.agda) derives exercise 7.16 in both directions. Taking an `R`-minimum among the `S`-minima gives the same candidates as comparing first by `S` and applying `R` on ties. Transitivity of `S` suffices for the concrete relation proof.

[MinimalComparison](../src/AoP/MinimalComparison.agda) checks exercise 7.19. The comparison `R b a → R a b` used to test minimality is reflexive. A three-element preorder with one strict edge and an isolated point shows why this comparison can fail transitivity.

[MinimalInclusion](../src/AoP/MinimalInclusion.agda) answers exercise 7.21 with a counterexample. Under equality, `high` is minimal in the full three-point set. Adding `low ≤ high` makes `low` a strict predecessor, so `high` loses minimality on that same set.

[MinimalSymmetry](../src/AoP/MinimalSymmetry.agda) proves exercise 7.23. Every member of every set is minimal exactly when the comparison relation is symmetric. For the converse, testing minimality on the full set reverses any given edge.

[MinimalImage](../src/AoP/MinimalImage.agda) proves exercise 7.22. The minimal elements of an image are exactly the images of source elements minimal under the pulled-back comparison. Image membership supplies the required preimage even when the function is not injective.

[MinimalSum](../src/AoP/MinimalSum.agda) proves exercise 7.24. For the sum of two relations, a left-tagged element is minimal exactly when it is minimal among the left-tagged members under the left relation; the right-tagged case is symmetric. The proof uses the fact that every incoming edge preserves its tag.

[WellBounded](../src/AoP/WellBounded.agda) proves the connectedness part of 7.26 by taking a minimum of `{a,b}`. For 7.27 a minimum of the function image supplies a source witness for the pulled-back relation. For 7.28 every member lies above some minimum exactly when every inhabited set has a minimum. [StrictBoundCounterexample](../src/AoP/StrictBoundCounterexample.agda) refutes the converse strict-part claim for unrestricted preorders: equality on two points has an empty, well-founded strict part, but the two-point set has no minimum. A corrected equivalence with additional hypotheses remains open.

The complete exercise and worked-example inventory for this chapter remains open. Existing case-study entry points include [PartyExample](../src/AoP/PartyExample.agda), [CylinderExample](../src/AoP/CylinderExample.agda), and [VanExample](../src/AoP/VanExample.agda).
