# Chapter 4: relations

This inventory covers exercises 4.1–4.18 (§§4.1–4.2). [Relations](../src/AoP/Relations.agda) represents an edge by a witness and a composite by two edges with a shared intermediate point. For example, two Boolean-valued choices can lead to the same final output through different intermediate values. Exercise 4.3 shows exactly where that difference matters.

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
| 4.11 | Open: derive the chain of equalities for a test intersected with identity. |
| 4.13–4.14 | [PartialEquivalence](../src/AoP/PartialEquivalence.agda): symmetric transitive relations are idempotent; symmetry and transitivity together are equivalent to `R = R ∘ R˘`. |
| 4.15 | [SimpleZigzag](../src/AoP/SimpleZigzag.agda): simplicity collapses a zigzag; allowing both Boolean outputs disproves the converse. |
| 4.16 | [RangeRotation](../src/AoP/RangeRotation.agda): expose the same range by exchanging triangle witnesses. |
| 4.17 | [DomainPullback](../src/AoP/DomainPullback.agda): pull a domain test back along a function graph. |
| 4.18 | Open: construct the allegory of locale-valued relations. |

The witness calculations above establish the laws in concrete `Rel`. Their derivations from abstract allegory axioms, the remaining sections, and the full inventory of unnumbered examples remain open.
