# Chapter 5: relational datatypes

This inventory covers exercises 5.1–5.19 (§§5.1–5.5). A relator lifts a relation on elements to one on structured values. [ExponentialRelator](../src/AoP/ExponentialRelator.agda), for example, relates two indexed families when their entries are related at every index. [RelationalProducts](../src/AoP/RelationalProducts.agda) relates pairs by independent choices in the two coordinates.

| Exercise | Construction and scope |
| --- | --- |
| 5.1 | Open: exhibit a non-monotone endofunctor on `Rel`. |
| 5.2 | [RelatorTests](../src/AoP/RelatorTests.agda) derives meet preservation for coreflexive tests from composition and monotonicity. [PowerMeetFailure](../src/AoP/PowerMeetFailure.agda) uses Boolean identity and negation to refute unrestricted meet preservation. |
| 5.3 | [ExponentialRelator](../src/AoP/ExponentialRelator.agda): lift relations pointwise to indexed families, using pointwise equality for the identity relation on families. |
| 5.4 | Open: derive the arrow action of the empty/nonempty functor and prove the obstruction to extending it to a relator. |
| 5.5 | [RelatorDomain](../src/AoP/RelatorDomain.agda): identify the domain of a lifted relation using the lifted domain test and a witness for an outgoing edge. |
| 5.6 | [RelationalProducts](../src/AoP/RelationalProducts.agda) checks componentwise composition in `Rel`. The requested derivation using only laws (5.4) and (5.2) remains open. |
| 5.7–5.8 | [RelationalPairing](../src/AoP/RelationalPairing.agda): separate paths that share an intermediate input; push independent component steps into both branches and reassemble them. |
| 5.9 | [PairInput](../src/AoP/PairInput.agda): distribute an input function into both branches. Replacing it with a relation that chooses either Boolean admits a mixed pair on only one side. |
| 5.10 | Open: derive naturality of `unzip` for a general relator. |
| 5.11 | [RelationalCurry](../src/AoP/RelationalCurry.agda): construct evaluation for the relational tensor and prove that currying gives the unique solution up to mutual inclusion. |

In §5.3, [InjectionTests](../src/AoP/InjectionTests.agda) checks the identities in exercise 5.12 for concrete relations. The left and right partial projections accept only the matching tag. Reinjecting their results recovers identity, and the union of the two branches recovers any copair. The abstract derivation via Proposition 4.1 remains open.

[CopairCancellation](../src/AoP/CopairCancellation.agda) checks equation 5.11 (exercise 5.13) in `Rel`. The intermediate point carries a tag, so its path belongs to exactly one branch of the construction. The result is the union of the two component composites. The relational tensor used for products has pairs of intermediate points; reversing arrows preserves that tensor rather than turning it into a tagged union.

[SumRestriction](../src/AoP/SumRestriction.agda) checks exercise 5.14: a step in the relational sum keeps its tag, so a common observation restricting that step need only be tested in the matching branch. Both inclusions retain the same observation witness.

In §5.4, [ImageNotRelator](../src/AoP/ImageNotRelator.agda) checks the obstruction in exercise 5.15. Adding the sole edge on a singleton changes the image of the full input from empty to full. The graph of the image function therefore loses its old output, violating monotonicity in the relation. Agreement on functions alone cannot identify it with the power relator.

[ImageDomainCover](../src/AoP/ImageDomainCover.agda) checks exercise 5.16. Passing the lifted domain test supplies an output for every input member. An output in the existential image already has an input witness. These two facts give both coverage conditions of the power relator.

[GuardCases](../src/AoP/GuardCases.agda) checks exercise 5.17 for concrete relations and decidable predicates. Each input receives exactly one branch tag. Refining a guarded conditional is equivalent to refining each branch on the inputs that reach it.

[ListMeet](../src/AoP/ListMeet.agda) checks the cons-list case of exercise 5.18. Two alignments of the same lists have matching constructors, so each pair of element witnesses can be combined into a witness for their intersection. The theorem for general binary relators remains open.

[EntireFold](../src/AoP/EntireFold.agda) checks the cons-list instance of exercise 5.19: an entire list algebra supplies a base value and a successor for each head and reduced tail, yielding a fold result for every input list. The general proof by reflection remains open.

[TransposeCombinations](../src/AoP/TransposeCombinations.agda) checks exercise 5.20. For a given input, the outputs of a union form the union of the two output sets; intersection works analogously. For independent inputs, the possible output pairs form the Cartesian product.

[ListSetify](../src/AoP/ListSetify.agda) checks exercises 5.21–5.22. Treating a list as its membership predicate turns nil into the empty set, a singleton list into a singleton set, cons into union with a singleton, and map into direct image. Applying the same operation to the subsequence enumeration yields exactly the subsequence relation at the given input.

[SupersequenceFold](../src/AoP/SupersequenceFold.agda) checks exercise 5.23. The empty input permits any supersequence. Each required head permits an arbitrary prefix before its matching occurrence. The proof converts these witnesses in both directions to the skip/keep subsequence specification.

[InitFold](../src/AoP/InitFold.agda) checks exercise 5.24: folding a nonempty list with an empty singleton result and a cons step removes exactly its last element. The proof reconstructs the input by appending the discarded element and shows that any such decomposition yields the same prefix.

[PartitionFlatten](../src/AoP/PartitionFlatten.agda) checks exercise 5.26: the enumeration returns a list of nonempty blocks exactly when flattening those blocks gives the original input. The empty input has one partition, the empty list of blocks. For a nonempty candidate the completeness proof removes either its first singleton block or the first element of a longer block, reconstructing the `new` or `glue` step.

[PermuteTail](../src/AoP/PermuteTail.agda) checks the identity in exercise 5.28 for the insertion-based permutation relation: permuting the tail first leaves the set of final permutations unchanged. The derivation from the book’s `bagify` equation remains open.

[InterleaveFold](../src/AoP/InterleaveFold.agda) checks exercise 5.29. A fold assigns each output entry to one of two lists while preserving order in each. Its converse agrees in both directions with consuming the next head of either input. The book’s example interleaves `[1,2,3,4]` and `[10,11,12]` to obtain `[1,10,2,3,11,12,4]`.

Later sections and the unnumbered calculations still need a full audit.
