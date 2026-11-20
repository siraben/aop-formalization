# Chapter 8: dynamic programming

## §8.1 Thinning

Thinning retains a subset of candidates. Each original candidate must have a retained candidate that is at least as good under the chosen relation. For example, when the relation is equality, removing the last representative of a value would leave that value uncovered.

| Exercise | Construction and scope |
| --- | --- |
| 8.1 | [ThinIdentity](../src/AoP/ThinIdentity.agda) proves both directions: thinning by equality is exactly extensional equality of the input and output sets. |
| 8.2 | [Thinning](../src/AoP/Thinning.agda) proves reflexivity and transitivity of thinning from the corresponding laws of the comparison relation. |
| 8.3 | `min-after-thin` in [Thinning](../src/AoP/Thinning.agda) lifts a retained minimum to the original set using comparison inclusion and transitivity of the objective. |
| 8.4 | [ThinUnion](../src/AoP/ThinUnion.agda) shows that adding back any subset of the original candidates preserves a thinning. It proves the intermediate union membership inclusion. When the comparisons coincide, taking the same thinning twice witnesses the reverse inclusion up to extensional equality. |

The numbered exercise and intermediate derivation inventory for the rest of Chapter 8 remains open.
