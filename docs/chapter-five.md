# Chapter 5: relational datatypes

This inventory covers exercises 5.1–5.11 (§§5.1–5.2). A relator lifts a relation on elements to one on structured values. [ExponentialRelator](../src/AoP/ExponentialRelator.agda), for example, relates two indexed families when their entries are related at every index. [RelationalProducts](../src/AoP/RelationalProducts.agda) relates pairs by independent choices in the two coordinates.

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

Later sections and the unnumbered calculations still need a full audit.
