# Chapter 4: relations

This inventory covers exercises 4.1–4.27 (§§4.1–4.3). [Relations](../src/AoP/Relations.agda) represents an edge by a witness and a composite by two edges with a shared intermediate point. For example, two Boolean-valued choices can lead to the same final output through different intermediate values. Exercise 4.3 shows exactly where that difference matters.

| Exercise | Construction and scope |
| --- | --- |
| 4.1 | [IndirectMeet](../src/AoP/IndirectMeet.agda): compare the lower bounds of both bracketings to derive associativity from the meet universal property. |
| 4.2 | Open: translate the two diagrams into inequations. |
| 4.3 | [MeetWitness](../src/AoP/MeetWitness.agda): prove the forward distribution inclusion and refute its converse with incompatible Boolean witnesses. |
| 4.4 | [MeetTerminal](../src/AoP/MeetTerminal.agda): construct the thin category of common lower bounds and its terminal intersection. |
| 4.5–4.6 | [ModularRefinement](../src/AoP/ModularRefinement.agda): keep a witness through a modular restriction; turn one edge into a three-edge zigzag. |
| 4.7 | Open: construct the product of two allegories. |
| 4.8–4.9 | [CoreflexiveMeet](../src/AoP/CoreflexiveMeet.agda): composing two coreflexive relations gives their intersection; taking the same relation twice yields transitivity. |
| 4.10, 4.12 | [RangeTest](../src/AoP/RangeTest.agda): move an output test through intersection or range. |
| 4.11 | [DiagonalTest](../src/AoP/DiagonalTest.agda): reduce all five expressions to the same condition: the test accepts the state and the relation has a loop there. |
| 4.13–4.14 | [PartialEquivalence](../src/AoP/PartialEquivalence.agda): symmetric transitive relations are idempotent; symmetry and transitivity together are equivalent to `R = R ∘ R˘`. |
| 4.15 | [SimpleZigzag](../src/AoP/SimpleZigzag.agda): simplicity collapses a zigzag; allowing both Boolean outputs disproves the converse. |
| 4.16 | [RangeRotation](../src/AoP/RangeRotation.agda): expose the same range by exchanging triangle witnesses. |
| 4.17 | [DomainPullback](../src/AoP/DomainPullback.agda): pull a domain test back along a function graph. |
| 4.18 | Open: construct the allegory of locale-valued relations. |

## §4.3: tabulations

[Tabulation](../src/AoP/Tabulation.agda) gives a table one row per witnessed edge. Reading its source and target columns reconstructs the relation. Joint injectivity of the columns follows when evidence for any given edge is unique.

| Exercise | Construction and scope |
| --- | --- |
| 4.19 | [MonicKernel](../src/AoP/MonicKernel.agda): a function is monic exactly when two inputs sharing an output must be equal. |
| 4.20 | [ImageComparison](../src/AoP/ImageComparison.agda): two given surjective/injective factorizations have a unique comparison isomorphism in `Fun`, using supplied preimages. Constructing a factorization for every function remains open. |
| 4.21–4.23 | [TabulatedFunction](../src/AoP/TabulatedFunction.agda): simplicity makes the source column injective for a jointly injective table. Totality supplies a row for each input. Together these yield both inverse laws. |
| 4.24 | [EntireBridge](../src/AoP/EntireBridge.agda): each row can be connected to an intermediate value exactly when the span lies in the composite relation. |
| 4.25 | Open: determine when locale-valued relations admit tabulations. |
| 4.26–4.27 | [UnitRange](../src/AoP/UnitRange.agda): range reflects inclusion for relations from a singleton; composing with the universal relation and intersecting with identity gives the domain test. |

## §4.4: local completeness and Galois connections

[MeetFromJoin](../src/AoP/MeetFromJoin.agda) constructs the meet in exercise 4.28 for a small ordered carrier: take the join of all common lower bounds, then verify both clauses of the greatest-lower-bound property.

[RangeJoins](../src/AoP/RangeJoins.agda) proves exercise 4.29 for small indexed families in `Rel`: taking range commutes with union because the input witness and the branch index can be supplied in either order.

[RelDifference](../src/AoP/RelDifference.agda) checks exercise 4.30 for concrete relations. The universal property uses decidability of membership in the subtracted relation to recover a cover. The four difference identities record where such a decision is needed.

[EmptyRange](../src/AoP/EmptyRange.agda) checks exercise 4.31 in `Rel`: a relation is empty exactly when its range is empty. Exchanging the two input witnesses around a triangle then proves that `(R ∘ S) ⊓ T` is empty exactly when `R ⊓ (T ∘ S˘)` is empty.

[RelImplication](../src/AoP/RelImplication.agda) checks exercise 4.32 in `Rel`. At each pair of endpoints, implication turns an `R` witness into an `S` witness. The proof gives its universal property and both inclusions for each of the four identities.

[ImplicationPullback](../src/AoP/ImplicationPullback.agda) proves exercise 4.33 for function graphs: changing both endpoints before forming an implication gives the same relation as changing them afterwards.

[MeetConnection](../src/AoP/MeetConnection.agda) checks exercise 4.39: the diagonal map is left adjoint to binary meet in the componentwise product order. It derives the adjunction from the meet projections and pairing, recovers both laws, and proves monotonicity of the two maps.

[AdjointJoins](../src/AoP/AdjointJoins.agda) checks both directions of exercise 4.40 for monotone `f` on orders with small indexed joins. Given an adjunction, `f` preserves joins and `g y` is the join of the inputs whose images lie below `y`. Conversely, join preservation makes that join itself admissible, yielding `f x ≤ y` exactly when `x ≤ g y`. The rest of §4.4 still needs an exercise-by-exercise inventory.

The witness calculations above establish the laws in concrete `Rel`. Their derivations from abstract allegory axioms, the remaining sections, and the full inventory of unnumbered examples remain open.
