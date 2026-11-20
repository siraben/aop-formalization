# Chapter 7: optimisation problems

## §7.1 Minimum and maximum

[SubsetBounds](../src/AoP/SubsetBounds.agda) checks exercises 7.1–7.2 for concrete predicates. A lower bound for a superset also bounds the subset; taking the subset itself proves the converse factorization. A set lies in the subset relation to an existential image exactly when each of its members has a related preimage in the source set.

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

[UnionMinimum](../src/AoP/UnionMinimum.agda) proves the union law in exercise 7.29 for indexed families. The minima of the union are exactly the minima of the union of the local minima. Empty member sets contribute no candidates. [ListMinimumFold](../src/AoP/ListMinimumFold.agda) checks the resulting singleton-and-cons recurrence against minima of list membership in both directions. A cons compares its head with a winner of the tail, permitting both choices on a tie. The empty list has no winner.

[WellSupported](../src/AoP/WellSupported.agda) checks exercises 7.30–7.31. Every minimum is minimal, whereas equality on two points has a minimal member in every inhabited subset without having a minimum in the full set. Under a well-supported preorder, restricting attention to predecessors of a given member produces a minimal element below it that is also minimal in the original set.

[UnionMinimal](../src/AoP/UnionMinimal.agda) proves exercise 7.32 for indexed families under a well-supported preorder. Keeping all local minimal elements preserves the global minimal elements, including ties and incomparable candidates. For a discarded challenger, exercise 7.31 supplies a retained one below it.

[ConnectedMinima](../src/AoP/ConnectedMinima.agda) checks exercise 7.20. Every minimum is minimal, and for a connected comparison every minimal element is a minimum. Equality of the two predicates does not force transitivity: the reflexive three-cycle is connected but fails the transitivity test.

[ResidualFactor](../src/AoP/ResidualFactor.agda) checks exercise 7.3 for concrete relations. The set of intermediate values related to a fixed output by `R` witnesses the factorization; conversely, each witness from the intermediate set composes with its `S` edge.

[LiftBound](../src/AoP/LiftBound.agda) proves exercise 7.4 using the factorization from 7.3. Intersect the intermediate set with the image of the source set: each source still has a witness, and every retained intermediate value now has a source. These are the two coverage conditions of the power relator.

[LiftMinimum](../src/AoP/LiftMinimum.agda) proves the inclusion in exercise 7.18 for concrete relations with reflexive comparison. Add the reachable candidate to the intermediate set of 7.4. Its incoming edge preserves backward coverage, and reflexivity gives the missing comparison with itself, turning the lower bound into a minimum.

The unnumbered §7.1 implementation [BinaryMinimum](../src/AoP/BinaryMinimum.agda) returns one minimum of a nonempty list under a decidable connected preorder. A successful head comparison selects the head, including on ties; in the other branch connectedness proves that the tail winner precedes the head. Each result carries input membership and its lower-bound proof.

[SupremumThreshold](../src/AoP/SupremumThreshold.agda) checks exercise 7.17 for a preorder. An element is the least upper bound exactly when the upper bounds are all and only the elements above it. In the converse direction, reflexivity at the candidate proves that it is itself an upper bound.

[MinimalTieClass](../src/AoP/MinimalTieClass.agda) checks exercise 7.25 with the candidate as representative of its primary tie class. Among the `R`-minimal elements tied with that candidate, `S` decides minimality for the combined comparison. Extracting primary minimality uses decidability of `R`; combining the two stages uses only the preorder laws.

## §7.2 Monotonic algebras

[SumOfMinima](../src/AoP/SumOfMinima.agda) verifies the unnumbered addition example. Given minima `m` and `n` of two sets of natural numbers, their sum is attainable and bounds every pairwise sum below. The bound is exactly the componentwise monotonicity of addition.

[OneWayMonotone](../src/AoP/OneWayMonotone.agda) gives the intermediate §7.2 counterexample for relational monotonicity. The high input can return an extra low output. Every increase in input permits a matching increase or equality in output, but the reverse comparison cannot match that extra output.

[AdditionReflection](../src/AoP/AdditionReflection.agda) checks exercise 7.33. Pulling a comparison back along addition of a fixed natural number reflects the comparison to the original arguments. The proof strips the common successors and supplies the point-free inclusion for both strict and non-strict order.

The complete exercise and worked-example inventory for this chapter remains open. Existing case-study entry points include [PartyExample](../src/AoP/PartyExample.agda), [CylinderExample](../src/AoP/CylinderExample.agda), and [VanExample](../src/AoP/VanExample.agda).
